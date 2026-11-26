-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_fastPlane_of_isUnknotted_of_selfLinking
-- name    : FiniteEnergyPlane.exists_fastPlane_of_isUnknotted_of_selfLinking
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T23:15:42.303705+00:00
-- url     : https://prove2.me/theorems/91586799-5507-552a-b803-e8e0be6acff9
-- title:
--   Existence of an embedded fast plane over an unknotted orbit of self-linking number $-1$
-- statement:
--   Let $S_0=H_0^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, and let $P=(x,T)$ be a prime, unknotted periodic orbit of $X_{H_0}$ on $S_0$ with self-linking number $\mathrm{sl}(P)=-1$. Let $H_k\to H_0$ in $C^\infty_{loc}(\mathbb{R}^4)$, with strictly star-shaped levels $S_k=H_k^{-1}(1)$, such that
--
--   1. every periodic orbit on every $S_k$ is nondegenerate;
--   2. $H_k=H_0$ and $dH_k=dH_0$ at the points of $x(\mathbb{R})$;
--   3. for every $A$ there is $K$ such that for $k\ge K$ all periodic orbits on $S_k$ of action at most $A$ satisfy $\mu_{CZ}\ge3$.
--
--   Then for all large $k$ the orbit $P$ of $X_{H_k}$ on $S_k$ has the image of a prime periodic Reeb orbit $Q$, whose period is the action of $P$, and
--   $$\exists\,J\ \exists\,u:\mathbb{C}\to\mathbb{R}^4\quad u\ \text{is an embedded fast finite-energy }\tilde J\text{-holomorphic plane asymptotic to }Q\text{ at }\infty ,$$
--   where $J$ is a smooth $d\lambda_0$-compatible complex structure on the contact planes of $S_k$.
--
--   The level $S_0$ may be degenerate; the planes are found in the approximating levels, which have the orbit $P$ in common.
--
--   **Formalization Note** The conclusion is for every `PeriodicOrbit` `Pk` of $H_k$ with the map and period of $P$; such an orbit exists by 2. Periodic orbits $P$ of $X_{H_0}$ are those of `HryniewiczCriterion_Basic`, in the coordinates `R4`; the level and the orbit are transported by the coordinate-preserving identification `ofR4` with `V 1`. Unknotted is `IsUnknotted`, the self-linking number is `HasSelfLinkingNumber`, and 1 and 3 are stated for every linearized flow and every period. Nothing is assumed about periodic orbits on $S_0$ other than $P$, and no dynamical convexity of $S_0$. The plane is `IsFastPlane`, `IsEmbeddedPlane` and, at $\infty$, `IsNondegenerateEnd` with sign $1$. In the source $\lambda$ is dynamically convex, which yields 3 for approximations of it.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), 791–862, arXiv:1105.2077, Theorem 3.4

import Definitions.Def_FiniteEnergyPlane_DiskFoliation
import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hryniewicz (2014), Theorem 3.4. Let `P` be a prime unknotted
periodic orbit of self-linking number `-1` on a strictly star-shaped level of `H₀`, and let `Hs k → H₀` in `C^∞_loc`, with strictly
star-shaped nondegenerate levels, agree with `H₀` to first order along `P`. Suppose that for every `A` all periodic
orbits of `Hs k` of action at most `A` have Conley–Zehnder index at least `3` when `k` is large. Then for all large `k` the orbit
`P` of `Hs k` is, in `V 1`, the image of a prime periodic Reeb orbit `Q` whose period is the action of `P`, and for
some compatible `J` there is an embedded fast finite-energy `J̃`-holomorphic plane asymptotic to `Q` at `∞`. -/
theorem exists_fastPlane_of_isUnknotted_of_selfLinking (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) (P : HryniewiczCriterion.PeriodicOrbit H₀)
    (hP : P.IsPrime) (hu : HryniewiczCriterion.IsUnknotted H₀ P)
    (hsl : HryniewiczCriterion.HasSelfLinkingNumber H₀ P (-1))
    (Hs : ℕ → HryniewiczCriterion.R4 → ℝ)
    (hSk : ∀ k, HryniewiczCriterion.IsStrictlyStarShapedLevel (Hs k))
    (hnd : ∀ k (R : HryniewiczCriterion.PeriodicOrbit (Hs k))
      (Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4)),
      HryniewiczCriterion.IsLinearizedFlow (Hs k) R.x Y → ∀ v : Fin 2 → ℝ,
      (HryniewiczCriterion.linearizedXiPath (Hs k) R Y 1).mulVec v = v → v = 0)
    (hjet : ∀ k, ∀ y ∈ P.image, Hs k y = H₀ y ∧ fderiv ℝ (Hs k) y = fderiv ℝ H₀ y)
    (hconv : ∀ m : ℕ, ∀ K : Set HryniewiczCriterion.R4, IsCompact K →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (Hs k)) (iteratedFDeriv ℝ m H₀) atTop K)
    (hcz : ∀ A : ℝ, ∃ K : ℕ, ∀ k, K ≤ k → ∀ (R : HryniewiczCriterion.PeriodicOrbit (Hs k))
      (Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4)),
      HryniewiczCriterion.IsLinearizedFlow (Hs k) R.x Y →
      (∫ t in (0 : ℝ)..R.T, HryniewiczCriterion.liouvilleForm (R.x t) (deriv R.x t)) ≤ A →
      3 ≤ HryniewiczCriterion.czIndexOfPath (HryniewiczCriterion.linearizedXiPath (Hs k) R Y)) :
    ∃ K : ℕ, ∀ k, K ≤ k → ∀ Pk : HryniewiczCriterion.PeriodicOrbit (Hs k), Pk.x = P.x → Pk.T = P.T →
      let H : V 1 → ℝ := fun y => Hs k (fun k => y (Fin.cast (by norm_num) k))
      ∃ Q : ReebOrbit H, Q.IsPrime ∧ Set.range Q.x = Set.range (fun τ => ofR4 (Pk.x τ)) ∧
        Q.T = ∫ τ in (0 : ℝ)..Pk.T, liouville (ofR4 (Pk.x τ)) (deriv (fun s => ofR4 (Pk.x s)) τ) ∧
        ∃ J : V 1 → V 1 →L[ℝ] V 1, IsCompatibleXiStructure H J ∧ ∃ u₀ : ℂ → V 1,
          IsFastPlane H J u₀ ∧ IsNondegenerateEnd H u₀ cylInf Q 1 ∧ IsEmbeddedPlane u₀ := by
  sorry

end FiniteEnergyPlane
