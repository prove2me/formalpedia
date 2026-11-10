-- Prove2me | Theorems.Thm_DNFSatMQ_Main_theorem_9_1
-- name    : DNFSatMQ.Main.theorem_9_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:34:18.500207+00:00
-- url     : https://prove2.me/theorems/bd9de4f3-afc6-4282-aee5-fd7a8f34e2df
-- title:
--   Theorem 9.1 — KM algorithm: θ-accurate sparse approximation of all Fourier coefficients from oracle access
-- statement:
--   Let $g : \{0,1\}^d\to[-1,1]$ with $d\ge1$, and $\theta,\delta\in(0,1)$. Given oracle access to $g$, the randomized algorithm $\mathrm{KM}(g,\theta,\delta)$ returns a vector $\tilde g$, represented by its nonzero entries, such that with probability at least $1-\delta$
--   $$\|\hat g-\tilde g\|_\infty\le\theta,\qquad \|\tilde g\|_0\le\frac4{\theta^2},$$
--   where $\hat g(A) = \mathbb E_{x\sim U_d}[g(x)\chi_A(x)]$, $\chi_A(x) = (-1)^{\sum_{i\in A}x_i}$. Its running time and number of oracle queries are $\tilde O(d^2\theta^{-6}\log(1/\delta))$ and $\tilde O(d\theta^{-6}\log(1/\delta))$. This result is cited by the paper ([KM93]; [Fel12, Theorem 1]) and used inside Feldman's learner (Theorem 8.1, Appendix A).
--
--   In Lean: one program and one constant $C$ such that, for every input, every run halts within $\lceil C\,d^2\theta^{-6}(1+\ln(1/\delta))\,\Lambda^C\rceil$ steps and asks at most $C\,d\,\theta^{-6}(1+\ln(1/\delta))\,\Lambda^C$ queries to $g$, with $\Lambda = 1+\ln(d\,\theta^{-1}(1+\ln(1/\delta)))$, every run outputs a decodable list of distinct nonzero entries, and with probability $\ge 1-\delta$, the represented vector has both properties.
--
--   Differences from the source:
--   - encoding: coordinates [n] = {1, …, n} and bits {0, 1} → `Fin n` (coordinates 0, …, n−1) and `Bool`; reason: Lean convention; same instances
--   - reading: Õ(X) → C · X · Λ^C with Λ = 1 + ln(d θ⁻¹ (1 + ln(1/δ))), one constant C; reason: a polylogarithmic factor in d, 1/θ and log(1/δ), as the notation means
--   - reading: log(1/δ) inside Õ(…) → 1 + ln(1/δ); reason: literally the bounds tend to 0 as δ → 1 while any run costs at least one step; the asymptotic notation means max(1, log(1/δ)) up to a constant, which 1 + ln(1/δ) is
--   - generalization: oracle access to g with values in [−1, 1] → g any real-valued function into [−1, 1], queried by comparisons "g(x) ≤ v?" for rational v (`realOracle`); θ, δ likewise; reason: covers every exact or rational-valued oracle; a value to accuracy 2^{−k} costs k comparisons, a polylogarithmic factor
--   - encoding: a randomized algorithm and its running time → a program of the fair-coin RAM whose bounds hold for every coin-tape length L ≥ the time bound; reason: a randomized algorithm has an unbounded supply of coins
--   - encoding: g̃ represented by its nonzero entries → the output word starts with a list of entries (A, v), v rational, decoded by `decodeSparse`; g̃(A) is the first entry for A; reason: the representation of the paper
--   - encoding: fair random bits, with no additional input in the random-bit supply → HaltsWithin includes CoinsInBounds: every readCoin address is below the supplied tape length; reason: the RAM sentinel must not reveal the externally chosen resource bound; this also makes sampler behavior depend only on its output-word input and fair bits
--   - encoding: returns a vector represented by its nonzero entries → every run outputs a decodable list with distinct indices and nonzero rational values; reason: zero entries and repeated indices are omitted; approximation and support bounds remain joint success conditions
-- source:
--   Zelin Li, Learning DNF from Satisfying Assignments with Membership Queries, STOC 2027 submission (manuscript sha256 2e246dc4…2670), Theorem 9.1, p. 31 (PDF 32)

import Mathlib
import Definitions.Def_DNFSatMQ_Main_Machine
open TargetedSamplers

namespace DNFSatMQ.Main

/-- Theorem 9.1 (p. 31; KM algorithm, cited). `Õ(X)` is read as `C · X · polylog`, with the
polylogarithmic factor `(1 + log(d θ⁻¹ (1 + log(1/δ))))^C` and `log(1/δ)` read as
`1 + log(1/δ)`. -/
theorem theorem_9_1 :
    ∃ (P : Program) (C : ℕ), ∀ d : ℕ, 1 ≤ d → ∀ θ δ : ℝ, 0 < θ → θ < 1 → 0 < δ → δ < 1 →
      ∀ g : Pt d → ℝ, (∀ x, -1 ≤ g x ∧ g x ≤ 1) →
      ∀ L : ℕ,
        ⌈(C : ℝ) * ((d : ℝ) ^ 2 * θ⁻¹ ^ 6 * (1 + Real.log (1 / δ))) *
            (1 + Real.log (d / θ * (1 + Real.log (1 / δ)))) ^ C⌉₊ ≤ L →
        (∀ r : Fin L → Bool,
          HaltsWithin P (realTapes g θ δ r)
            ⌈(C : ℝ) * ((d : ℝ) ^ 2 * θ⁻¹ ^ 6 * (1 + Real.log (1 / δ))) *
              (1 + Real.log (d / θ * (1 + Real.log (1 / δ)))) ^ C⌉₊ ∧
          (mqCount P (realTapes g θ δ r) : ℝ) ≤
            C * ((d : ℝ) * θ⁻¹ ^ 6 * (1 + Real.log (1 / δ))) *
              (1 + Real.log (d / θ * (1 + Real.log (1 / δ)))) ^ C) ∧
        (∀ r : Fin L → Bool, ∃ y es,
          outWord P (realTapes g θ δ r) = some y ∧ decodeSparse d y = some es ∧
          (es.map Prod.fst).Nodup ∧ ∀ e ∈ es, e.2 ≠ 0) ∧
        probCoins L (fun r => ∃ y es, outWord P (realTapes g θ δ r) = some y ∧
          decodeSparse d y = some es ∧
          supDist (fourierCoeff g) (sparseVec es) ≤ θ ∧
          (l0Norm (sparseVec es) : ℝ) ≤ 4 / θ ^ 2) ≥ 1 - δ := by sorry

end DNFSatMQ.Main
