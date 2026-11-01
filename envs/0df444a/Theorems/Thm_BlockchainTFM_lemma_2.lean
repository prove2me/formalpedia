-- Prove2me | Theorems.Thm_BlockchainTFM_lemma_2
-- name    : BlockchainTFM.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:04:16.996304+00:00
-- url     : https://prove2.me/theorems/2201f0d9-0791-44b1-8fd2-7a15a4b8a3e3
-- title:
--   Lemma 2: the variation term (19)–(20) is admissible (corrected: $c_\rho=\mathbb E[v^2]$)
-- statement:
--   Let $n\ge2$ users have valuations i.i.d. from a law $V_0$ on $[0,1]$ with $c_\rho=\mathbb E_{v\sim V_0}[v^2]>0$, and let $h\in[0,+\infty)$. The variation term $T=(\boldsymbol\theta,\tilde r)$ of (19)–(20),
--   $$\theta_i(b_i,\mathbf b_{-i})=-\tfrac12hb_i^2\Bigl(\frac{\sum_{j\ne i}b_j^2}{c_\rho(n-1)}-1\Bigr),\qquad \tilde r(\mathbf b)=\tfrac12h\Bigl(\sum_{i=1}^nb_i^2-\frac{\sum_{1\le i<j\le n}b_i^2b_j^2}{c_\rho(n-1)}\Bigr),$$
--   is admissible: for every bid vector $\mathbf b\in[0,1]^n$ and every user $i$,
--   $$\tilde r(b_i,\mathbf b_{-i})-\tilde r(0,\mathbf b_{-i})=\theta_i(b_i,\mathbf b_{-i}),$$
--   and for every $b_i\in[0,1]$, $\theta_i(b_i,\cdot)$ is integrable with
--   $$\mathbb E_{\mathbf b_{-i}\sim V_{-i}}\bigl[\theta_i(b_i,\mathbf b_{-i})\bigr]=0.$$
--
--   Combined with Theorem 2, the lemma makes Mechanisms 2 and 3 U-BNIC and 1-SCP while paying the miner $\tilde r$, whose expectation is $\frac14hnc_\rho>0$.
--
--   **Formalization Note** $c_\rho$ is the second moment of $V_0$; the paper's (18) prints $\int_0^1\rho^2$, under which the lemma is false (see the correction below).
--
--   Differences from the source:
--   - correction: c_ρ = ∫₀¹ ρ²(t) dt (18) → c_ρ = ∫ t² dV₀(t) = E[v²] (crho); reason: with ∫ρ², (11) fails: n = 2, V₀ uniform gives ∫ρ² = 1 and E_{b₂}[θ₁(b₁,b₂)] = −½hb₁²(1/3 − 1) = hb₁²/3 ≠ 0 for h > 0, b₁ > 0; the paper's own proof (EC.44)–(EC.45), §7.2 (uniform ⇒ c_ρ = 1/3), §8 and (EC.71) (c_ρ ≤ 1) all use E[v²]
--   - generalization: V₀ has a pdf ρ on [0,1] → any probability measure V₀ on ℝ with V₀([0,1]) = 1 and c_ρ > 0; reason: the proofs use only E[v²] = c_ρ and v ∈ [0,1]; every law with a pdf on [0,1] has c_ρ > 0 and is an instance
--   - encoding: division by c_ρ(n − 1) in (19)–(20) → hypotheses n ≥ 2 and 0 < c_ρ; reason: the paper assumes n ≥ 2 (p.26); c_ρ = 0 only for V₀ = δ₀, where the mechanism is undefined
--   - encoding: E[θ_i(b_i, b_{−i})] = 0 → θ_i(b_i,·) integrable against V₀^{⊗n} and its integral 0; reason: integrability only excludes undefined expectations; it holds here
--   - encoding: users 1,…,n; b_{−i}; bids and values in [0,1] → Fin n; a vector b ∈ [0,1]ⁿ whose i-th entry is overwritten (Function.update); bids, values and deviations in Set.Icc 0 1; reason: Lean convention; same instances
-- source:
--   Chen, Simchi-Levi, Zhao, Zhou, Bayesian Mechanism Design for Blockchain Transaction Fee Allocation, arXiv:2209.13099v7, §5.2, Lemma 2, (19)–(20), p.26 (proof Appendix EC.4.2, pp.ec11–ec12)

import Mathlib
import Definitions.Def_BlockchainTFM_Model
import Definitions.Def_BlockchainTFM_Decomposition
import Definitions.Def_BlockchainTFM_Mechanism3

open MeasureTheory

namespace BlockchainTFM

/-- **Lemma 2** (with `c_ρ = E[v²]`), Chen–Simchi-Levi–Zhao–Zhou, arXiv:2209.13099v7, p.26. For
`n ≥ 2` users with valuations i.i.d. from `V₀` and every `h ∈ [0, +∞)`, the variation term
`T = (θ, r̃)` of (19)–(20) is admissible (Definition 8):
`r̃(b_i, b_{-i}) − r̃(0, b_{-i}) = θ_i(b_i, b_{-i})` for every `b ∈ [0,1]ⁿ` and
`E_{b_{-i}∼V_{-i}}[θ_i(b_i, b_{-i})] = 0` for every `b_i ∈ [0,1]`.

**Formalization Note.** `c_ρ` is `crho V₀ = ∫ t² dV₀` (the paper prints `∫ρ²`, under which (11)
fails; see `crho`). `V₀` is any probability measure carried by `[0,1]` with `c_ρ > 0` (the
paper's `V₀` has a density, which implies both). -/
theorem lemma_2 {n : ℕ} (hn : 2 ≤ n) (V₀ : Measure ℝ) [IsProbabilityMeasure V₀]
    (hV₀ : V₀ (Set.Icc 0 1) = 1) (hc : 0 < crho V₀) (h : ℝ) (hh : 0 ≤ h) :
    IsAdmissible V₀ (theta (n := n) h (crho V₀)) (minerRev h (crho V₀)) := by sorry

end BlockchainTFM
