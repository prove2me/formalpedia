-- Prove2me | Theorems.Thm_BlottoFPTAS_Main_lemma_5_5
-- name    : BlottoFPTAS.Main.lemma_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:42:29.590494+00:00
-- url     : https://prove2.me/theorems/d9fe1c25-636b-4db4-aa8d-16a165252334
-- title:
--   Lemma 5.5 — a finite rational candidate-bid set S, independent of ρ and P, loses at most z/64; its elements have O(Λ)-bit encodings
-- statement:
--   There are universal constants $C_0,k_0$ such that for $m\ge2$, $e=2^{-a}$ ($a\ge1$) and positive values $w$ summing to one there is a finite set $S\subseteq[0,1]\cap\mathbb Q$ containing $0$ and $1$ with: for every rational $\rho\in(0,1)$ with denominator at most $q$, both choices $(c,c')\in\{(1,\rho),(\rho,1)\}$ and every distribution $P$ on $X(c)$, there is a distribution $P^*$ on $X=\{x\in S^m:\sum_jx_j\le c\}$ with
--   $$U_w(P^*;c')\le U_w(P;c')+z/64.$$
--   Every element of $S$ has binary length at most $C_0\Lambda+C_0$, and $\Lambda\le C_0(\log_2q+(m/z)\log_2(m+2))+C_0$ and $\Lambda\le C_0(m/z)\log_2(2+m+1/z)^{k_0}+C_0$. Here $q$, $z=e/2048$ and $\Lambda$ are the parameters of Appendix C.2. The set depends on the common bound $q$, not on $\rho$ or $P$, which is what allows the computation of §5.2 to fix it in advance.
--
--   Differences from the source:
--   - reading: binary encoding length O(Λ); Λ = O(log q + (m/z) log(m + 2)) = Õ(m/z) → ≤ C₀Λ + C₀ and the two displayed bounds on Λ, with C₀, k₀ universal (chosen before m, a, w); reason: standard reading of O and Õ with universal constants
--   - encoding: a distribution P* on X → a strategy on X(c) all of whose bids lie in S almost surely; reason: Lean convention; same distributions
--   - generalization: the values v̂ of the reduced game (rationals with common denominator Q_v) on m < 18/e battlefields → any positive real values w summing to one, any m ≥ 2; reason: the proof (App. C.3) uses neither the denominator of v̂ nor m < 18/e; S and the parameters depend only on m and e; the reduced game is a special case
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), p. 33, Lemma 5.5

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_Game
import Definitions.Def_BlottoFPTAS_Main_Params

open MeasureTheory

namespace BlottoFPTAS.Main

/-- **Lemma 5.5** (Bichler, Ghosh, arXiv:2611.05221, held version sha256 cac3638e…, p. 33).
There are universal constants `C₀, k₀` such that, for `m ≥ 2` battlefields, `e = 2^{-a}` with
`a ≥ 1`, and positive values `w` summing to one, there is a finite set `S ⊆ [0, 1] ∩ ℚ`
containing `0` and `1` such that, for every rational `ρ ∈ (0, 1)` with denominator at most `q`,
both choices `(c, c′) ∈ {(1, ρ), (ρ, 1)}` and every distribution `P` on `X(c)`, some distribution
`P*` on `X = {x ∈ S^m : ∑_j x_j ≤ c}` has `U_w(P*; c′) ≤ U_w(P; c′) + z/64`. Every element of `S`
has binary length at most `C₀ Λ + C₀`, and `Λ ≤ C₀ (log₂ q + (m/z) log₂(m + 2)) + C₀` and
`Λ ≤ C₀ (m/z) log₂(2 + m + 1/z)^{k₀} + C₀` (`Λ = O(log q + (m/z) log(m+2)) = Õ(m/z)`). Here `q`,
`z = e/2048` and `Λ` are the parameters of Appendix C.2. -/
theorem lemma_5_5 :
    ∃ (C₀ : ℝ) (k₀ : ℕ), ∀ (m a : ℕ), 2 ≤ m → 1 ≤ a →
      ∀ w : Fin m → ℝ, (∀ j, 0 < w j) → ∑ j, w j = 1 →
        ∃ S : Finset ℚ, (∀ s ∈ S, 0 ≤ s ∧ s ≤ 1) ∧ (0 : ℚ) ∈ S ∧ (1 : ℚ) ∈ S ∧
          (∀ ρ : ℚ, 0 < ρ → ρ < 1 → ρ.den ≤ qDen m a →
            ∀ c c' : ℝ, ((c, c') = (1, (ρ : ℝ)) ∨ (c, c') = ((ρ : ℝ), 1)) →
              ∀ P : Measure (Fin m → ℝ), IsStrategy m c P →
                ∃ Pstar : Measure (Fin m → ℝ), IsStrategy m c Pstar ∧
                  Pstar {x | ∀ j, ∃ s ∈ S, x j = (s : ℝ)}ᶜ = 0 ∧
                  U w Pstar c' ≤ U w P c' + zR a / 64) ∧
          (∀ s ∈ S, (ratSize s : ℝ) ≤ C₀ * Lam m a + C₀) ∧
          (Lam m a : ℝ) ≤
            C₀ * (Real.logb 2 (qDen m a) + (m / zR a) * Real.logb 2 (m + 2)) + C₀ ∧
          (Lam m a : ℝ) ≤ C₀ * (m / zR a) * Real.logb 2 (2 + m + 1 / zR a) ^ k₀ + C₀ := by sorry

end BlottoFPTAS.Main
