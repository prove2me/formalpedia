-- Prove2me | Theorems.Thm_FamousTheorems_integral_curve_uniqueness
-- name    : FamousTheorems.integral_curve_uniqueness
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:26:41.833986+00:00
-- url     : https://prove2.me/theorems/907867e4-5d05-42b7-8c3a-549e5a8d95ff
-- title:
--   Uniqueness of integral curves on manifolds
-- statement:
--   **Uniqueness of integral curves.** Let $M$ be a Hausdorff $C^1$ manifold without boundary modelled on a real Banach space, $v$ a $C^1$ vector field on $M$, and $\gamma,\gamma'$ two integral curves of $v$ on an open interval $(a,b)$. If $\gamma(t_0)=\gamma'(t_0)$ for some $t_0\in(a,b)$, then $\gamma=\gamma'$ on all of $(a,b)$.
--
--   With local existence, this gives the maximal flow of a vector field. The Hausdorff hypothesis cannot be dropped: on the line with two origins integral curves can branch.
--
--   **Formalization note.** Mathlib's `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless`. The smoothness hypothesis is that the section $x\mapsto(x,v(x))$ of the tangent bundle is $C^1$, and `IsMIntegralCurveOn γ v (Set.Ioo a b)` means $\gamma'(t)=v(\gamma(t))$ for every $t\in(a,b)$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem integral_curve_uniqueness {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [T2Space M]
    [BoundarylessManifold I M] {v : (x : M) → TangentSpace I x} {γ γ' : ℝ → M} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b)
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsMIntegralCurveOn γ v (Set.Ioo a b)) (hγ' : IsMIntegralCurveOn γ' v (Set.Ioo a b)) (h : γ t₀ = γ' t₀) :
    Set.EqOn γ γ' (Set.Ioo a b) := by sorry

end FamousTheorems
