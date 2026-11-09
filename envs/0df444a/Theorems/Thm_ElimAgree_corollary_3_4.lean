-- Prove2me | Theorems.Thm_ElimAgree_corollary_3_4
-- name    : ElimAgree.corollary_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:21:34.309204+00:00
-- url     : https://prove2.me/theorems/8b8e4af9-fadc-4831-94e2-31d24c35067a
-- title:
--   Corollary 3.4 — $H^2(q_+,q_-)\le\frac4\ell\ln\frac1p$
-- statement:
--   Let $U_1,\dots,U_r$ be finite sets of size $2\ell$ ($\ell\ge1$), let $\pi=\bigotimes_iu^{U_i}_\ell$, and let $P=\pi(\cdot\mid A)$ for a set $A$ of tuples of $\ell$-sets with $\pi(A)=p>0$. Let $q_\pm$ be the law of $(J_1,\dots,J_r)$ when $X\sim P$ and each $J_i$ is drawn from $\kappa_\pm(X_i,\cdot)$ independently. Then
--   $$H^2(q_+,q_-)\le\frac4\ell\ln\frac1p,$$
--   where $H^2(p,q)=\sum_j(\sqrt{p_j}-\sqrt{q_j})^2$ is the squared Hellinger distance (no factor $\tfrac12$).
--
--   This is the Hellinger estimate used inside the proof of Theorem 3.6.
--
--   Differences from the source:
--   - encoding: |U_i| = 2ℓ with 4/ℓ in the bound (ℓ ≥ 1 implicit) → hypothesis 1 ≤ ℓ; reason: for ℓ = 0 the channels κ± are undefined
--   - encoding: P = π(· | A), q± laws of (J_1, …, J_r) → condLaw π A pushed through the tensor channel ⊗κ±; p written as Σ_{X∈A} π(X); reason: Lean convention; same objects
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Corollary 3.4, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_ElimAgree_IsLaw
import Definitions.Def_ElimAgree_halfSetChannel

open FoundationsRL.GeneralDM

namespace ElimAgree

/-- Corollary 3.4, Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission), p.8: let `U_1, …, U_r` have size `2ℓ`, let
`π = ⊗_i u_ℓ^{U_i}`, and let `P = π(· | A)` for a set `A` with `π(A) = p > 0`. Let `q±` be the
law of `(J_1, …, J_r)` when `X ∼ P` and each `J_i` is drawn from `κ±(X_i, ·)` independently.
Then `H²(q+, q−) ≤ (4/ℓ) ln(1/p)`, with `H²(p, q) = Σ_j (√p_j − √q_j)²`.

**Formalization Note.** `A` is a set of tuples of `ℓ`-subsets; `q±` is `P` pushed through the
tensor channel `⊗_i κ±`. `1 ≤ ℓ` is assumed (for `ℓ = 0` the channels are undefined). -/
theorem corollary_3_4 {r : ℕ} {U : Fin r → Type} [∀ i, Fintype (U i)] [∀ i, DecidableEq (U i)]
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hU : ∀ i, Fintype.card (U i) = 2 * ℓ)
    (A : Finset (∀ i, LSet (U i) ℓ))
    (hA : 0 < ∑ X ∈ A, prodLaw (fun i => uniformLaw (LSet (U i) ℓ)) X) :
    hellingerSq
        (pushLaw (condLaw (prodLaw (fun i => uniformLaw (LSet (U i) ℓ))) A)
          (tensorChannel (fun i => halfSetChannel (U := U i) ℓ true)))
        (pushLaw (condLaw (prodLaw (fun i => uniformLaw (LSet (U i) ℓ))) A)
          (tensorChannel (fun i => halfSetChannel (U := U i) ℓ false))) ≤
      4 / (ℓ : ℝ) *
        Real.log (1 / ∑ X ∈ A, prodLaw (fun i => uniformLaw (LSet (U i) ℓ)) X) := by sorry

end ElimAgree
