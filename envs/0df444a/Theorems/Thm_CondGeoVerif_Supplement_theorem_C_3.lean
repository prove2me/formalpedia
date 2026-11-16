-- Prove2me | Theorems.Thm_CondGeoVerif_Supplement_theorem_C_3
-- name    : CondGeoVerif.Supplement.theorem_C_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:13:26.071982+00:00
-- url     : https://prove2.me/theorems/2327a1f2-b2c7-4c84-81c5-775942c35f0d
-- title:
--   Theorem C.3 — disagreement below $\gamma_K$ forces the same rule and a matched frame, $\|V-\widetilde W\|_F\le\sqrt{2k}A_K\Delta$
-- statement:
--   Let $b,c$ be essential Boolean rules of ranks $1\le k,\ell\le K$, let $V\in\mathbb R^{d\times k}$ and $W\in\mathbb R^{d\times\ell}$ be orthonormal frames, $h_{b,V}(x)=b(\mathrm{sign}(V^\top x))$, and $X\sim N(0,I_d)$. With $A_K=8K\cdot4^K$ and $\gamma_K=2^{-3K}/(32K^2)$ from (C.1), if
--   $$\Delta:=P(h_{b,V}(X)\ne h_{c,W}(X))<\gamma_K,$$
--   then $k=\ell$ and there is a signed relabeling of the competing columns whose induced Boolean rule is exactly $b$. Denoting the relabeled competing frame by $\widetilde W$,
--   $$\|V-\widetilde W\|_F\le\sqrt{2k}\,A_K\Delta .$$
--   In particular, if $b=c$ then $r_b(V,W)=\min_{Q\in S_b}\|W-VQ\|_F\le\sqrt{2k}\,A_K\Delta$, where $S_b$ is the group of signed permutation symmetries of $b$.
--
--   This is the identifiability step that lets the verifier of Theorem C.7 handle every different-rule orbit with one risk test.
--
--   Differences from the source:
--   - encoding: a signed relabeling whose induced Boolean rule is exactly b → a bijection e : [k] → [ℓ] and sign flips s with c(τ) = b(σ) for every σ ∈ {−1, 1}^k, where τ_{e(i)} = σ_i flipped iff s_i, and W̃ = columns ±W_{e(i)}; reason: the induced rule of the relabeled frame, exactly on the cube; a bijection encodes k = ℓ
--   - encoding: in particular, if b = c then r_b(V, W) ≤ √(2k) A_K Δ → a second conjunct: for frames V, W' ∈ ℝ^{d×k} of the same rule b with disagreement < γ_K there is Q ∈ S_b with ‖W' − VQ‖_F ≤ √(2k) A_K Δ; reason: r_b is a minimum over the finite nonempty group S_b; the case b = c needs ℓ = k, which Lean states separately
--   - encoding: labels in {−1, 1}; a sign on a zero hyperplane can be chosen arbitrarily → labels Bool (true ↔ +1), sign(0) = +1; reason: hyperplanes are Gaussian-null, so no probability in the statement depends on the convention (App. C, p.28)
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Theorem C.3 and (C.1), p.29 (PDF p.32); proof p.30

import Mathlib
import Definitions.Def_CondGeoVerif_Supplement_boolComp

set_option autoImplicit false

open MeasureTheory ProjLikeRetr.Stiefel

namespace CondGeoVerif.Supplement

open CondGeoVerif

/-- **Theorem C.3 (Small disagreement forces the same rule and a matched frame)** (Chen, *The
Conditional Geometry of Statistical Verification*, manuscript, October 2026, sha256 07a66d18…,
p.29 = PDF p.32). Let `b, c` be essential rules with ranks `1 ≤ k, ℓ ≤ K`, and let `V ∈ ℝ^{d×k}`,
`W ∈ ℝ^{d×ℓ}` be orthonormal frames. If `Δ := P(h_{b,V}(X) ≠ h_{c,W}(X)) < γ_K`, `X ∼ N(0, I_d)`,
then `k = ℓ` and there is a signed relabeling of the competing columns whose induced Boolean rule is
exactly `b`; denoting the relabeled frame by `W̃`, `‖V − W̃‖_F ≤ √(2k) A_K Δ`. In particular, if
`b = c` then `r_b(V, W) ≤ √(2k) A_K Δ`. Here `A_K = 8K·4^K` and `γ_K = 2^{−3K}/(32K²)` (C.1).

**Formalization Note** The relabeling is a bijection `e : [k] → [ℓ]` (which forces `k = ℓ`) and sign
flips `s`: column `i` of `W̃` is `∓W_{·, e(i)}`. Since `sign(W_{e(i)}·x) = ±sign(W̃ᵢ·x)` off a null
set, the induced rule is `σ ↦ c(τ)` with `τ_{e(i)} = σᵢ` flipped iff `s i`; it equals `b` on every
`σ ∈ {−1, 1}ᵏ`. The `b = c` clause is the second conjunct, stated for the same rule `b`, frames
`V, W' ∈ ℝ^{d×k}`, and `r_b(V, W') = min_{Q ∈ S_b} ‖W' − VQ‖_F` read as the existence of a
minimizing `Q ∈ S_b` (a minimum over a finite nonempty set). -/
theorem theorem_C_3 {K k ℓ d : ℕ} (hk : 1 ≤ k) (hkK : k ≤ K) (hl : 1 ≤ ℓ) (hlK : ℓ ≤ K)
    (b : (Fin k → Bool) → Bool) (c : (Fin ℓ → Bool) → Bool) (hb : IsEssential b)
    (hc : IsEssential c) (V : Matrix (Fin d) (Fin k) ℝ) (W : Matrix (Fin d) (Fin ℓ) ℝ)
    (hV : V ∈ stiefel d k) (hW : W ∈ stiefel d ℓ)
    (hΔ : disagree (frameRule (boolComp b) V) (frameRule (boolComp c) W) < gammaK K) :
    (k = ℓ ∧ ∃ (e : Fin k ≃ Fin ℓ) (s : Fin k → Bool),
      (∀ σ : Fin k → Bool, c (fun j => xor (s (e.symm j)) (σ (e.symm j))) = b σ) ∧
      frob (V - relabel W e s) ≤
        Real.sqrt (2 * k) * AK K * disagree (frameRule (boolComp b) V) (frameRule (boolComp c) W)) ∧
    (∀ W' : Matrix (Fin d) (Fin k) ℝ, W' ∈ stiefel d k →
      disagree (frameRule (boolComp b) V) (frameRule (boolComp b) W') < gammaK K →
      ∃ Q ∈ symGroup b, frob (W' - V * Q) ≤
        Real.sqrt (2 * k) * AK K * disagree (frameRule (boolComp b) V) (frameRule (boolComp b) W')) := by sorry

end CondGeoVerif.Supplement
