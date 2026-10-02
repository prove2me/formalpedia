-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsD_l_convex_dir_deriv_subdifferential_correspondence
-- name    : DiscreteConvex.LConvexFunctionsD.l_convex_dir_deriv_subdifferential_correspondence
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:05:56.220681+00:00
-- url     : https://prove2.me/theorems/df60cee1-ae03-4a0f-9a25-72c38d767a28
-- title:
--   Theorem 7.43 -- l_convex_dir_deriv_subdifferential_correspondence
-- statement:
--   **Theorem 7.43** (p.196-197). (1) For $g\in L[\mathbb R\to\mathbb R]$ and $p\in\operatorname{dom}_{\mathbb R} g$, setting $\rho_{g,p}(X)=g'(p;\chi_X)$: $\rho_{g,p}\in S[\mathbb R]$, $\partial_{\mathbb R} g(p)=B(\rho_{g,p})$ is a nonempty M-convex polyhedron, and $g'(p;\cdot)=\hat\rho_{g,p}(\cdot)$. (2) The analogous statement for $g\in L[\mathbb Z\to\mathbb R]$ and $p\in\operatorname{dom}_{\mathbb Z} g$, with $\rho_{g,p}(X)=g(p+\chi_X)-g(p)$.
--
--   The L-side mirror of mission `24-ch06d-mconvexfunctions`'s goal (Theorem 6.61): the directional derivative, subdifferential, and base-polyhedron structure of a submodular set function are tied into a single correspondence.
--
--   **Formalization Note.** The book's own statement adds refined integrality clauses for the sub-classes $L[\mathbb R\to\mathbb R|\mathbb Z]$ and $L[\mathbb Z\to\mathbb Z]$ (e.g. $\rho_{g,p}\in S[\mathbb Z]$, $\partial_{\mathbb R} g(p)\in M_0[\mathbb Z|\mathbb R]$, $\partial_{\mathbb Z} g(p)\ne\emptyset$); these dual-integral refinements are not restated here, the same scope decision mission `24-ch06d-mconvexfunctions`'s Theorem 6.61 made — see `HARD.md`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.196-197, Theorem 7.43.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.196-197, Theorem 7.43

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IndicatorVec
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ConvexClosureVal
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DomR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_TRFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LovaszExtension
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_BasePolyhedron
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_MConvexPolyhedron
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_MConvexPolyhedronR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DirDeriv
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SubDifferentialR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SubDifferentialRZ

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.43 (p.196-197). The directional-derivative/subdifferential correspondence for
polyhedral and integer-domain L-convex functions, via the induced submodular set function and
its base polyhedron. Part (1) concludes in the real class `M⁰[R]`: for
`g(p) = (1/2) max(p₁ - p₂, 0)` the subdifferential at `0` is the segment from `(0,0)` to
`(1/2,-1/2)`, the convex hull of no integer set. Part (2), an integer-domain `g` at an integer
point, keeps the integral class. -/
theorem l_convex_dir_deriv_subdifferential_correspondence :
    (∀ g : (V → ℝ) → WithTop ℝ, (SBFR g ∧ TRFR g) → ∀ p ∈ DomR g,
      SubmodularSetFunction (fun X => DirDeriv g p (fun v => if v ∈ X then (1 : ℝ) else 0)) ∧
      SubDifferentialR g p =
        BasePolyhedron (fun X => DirDeriv g p (fun v => if v ∈ X then (1 : ℝ) else 0)) ∧
      MConvexPolyhedronR (SubDifferentialR g p) ∧
      (∀ d : V → ℝ, DirDeriv g p d =
        LovaszExtension (fun X => DirDeriv g p (fun v => if v ∈ X then (1 : ℝ) else 0)) d) ∧
      (SubDifferentialR g p).Nonempty) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, SBF g → ∀ p ∈ DomZ g,
      SubmodularSetFunction (fun X => g (fun v => p v + IndicatorVec X v) - g p) ∧
      SubDifferentialRZ g p =
        BasePolyhedron (fun X => g (fun v => p v + IndicatorVec X v) - g p) ∧
      MConvexPolyhedron (SubDifferentialRZ g p) ∧
      (∀ d : V → ℝ, DirDeriv (fun q => ConvexClosureVal g q) (fun v => (p v : ℝ)) d =
        LovaszExtension (fun X => g (fun v => p v + IndicatorVec X v) - g p) d) ∧
      (SubDifferentialRZ g p).Nonempty) := by sorry

end DiscreteConvex.LConvexFunctionsD
