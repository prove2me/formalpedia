-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsD_dir_deriv_subdifferential_correspondence
-- name    : DiscreteConvex.MConvexFunctionsD.dir_deriv_subdifferential_correspondence
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:53:26.502982+00:00
-- url     : https://prove2.me/theorems/7cb47821-4f94-4b07-99db-4aacfe70d229
-- title:
--   Theorem 6.61 -- dir_deriv_subdifferential_correspondence
-- statement:
--   **Theorem 6.61** (p.166-167). GOAL. (1) For $f\in M[\mathbb R\to\mathbb R]$ and $x\in\operatorname{dom}_{\mathbb R} f$, defining $\gamma_{f,x}(u,v)=f'(x;-\chi_u+\chi_v)$: $\gamma_{f,x}\in T[\mathbb R]$, $\partial_{\mathbb R} f(x) = D(\gamma_{f,x})$ is a nonempty L-convex polyhedron, and $f'(x;\cdot) = \hat\gamma_{f,x}(\cdot)$. (2) The analogous statement for $f\in M[\mathbb Z\to\mathbb R]$ and $x\in\operatorname{dom}_{\mathbb Z} f$, with $\gamma_{f,x}(u,v)=f(x-\chi_u+\chi_v)-f(x)$.
--
--   This ties together the directional derivative, the subdifferential, and the admissible-potential structure of chapter 5 into a single correspondence, the technical heart of the M-convex/L-convex duality developed further in Chapter 8.
--
--   **Formalization Note.** The book's own statement adds refined integrality clauses for the sub-classes $M[\mathbb R\to\mathbb R|\mathbb Z]$ and $M[\mathbb Z\to\mathbb Z]$ (e.g. $\partial_{\mathbb R} f(x) \in L_0[\mathbb Z|\mathbb R]$, $\partial_{\mathbb Z} f(x)\ne\emptyset$); these dual-integral refinements are not restated here — see `MODERATION_NOTES.md`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.166-167, Theorem 6.61.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.166-167, Theorem 6.61

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_DomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_DirDeriv
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_TriangleInequality
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_GammaHat
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_AdmissiblePotentials
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_SubDifferential
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_SubDifferentialR

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.61 (p.185-186). GOAL. -/
theorem dir_deriv_subdifferential_correspondence :
    (∀ f : (V → ℝ) → WithTop ℝ, MExchangeAxiomR f → ∀ x ∈ DomR f,
      TriangleInequality (fun u v => DirDeriv f x (fun w => (CharVec v w - CharVec u w : ℝ))) ∧
      SubDifferentialR f x =
        AdmissiblePotentials (fun u v => DirDeriv f x (fun w => (CharVec v w - CharVec u w : ℝ))) ∧
      (SubDifferentialR f x).Nonempty ∧
      (∀ d : V → ℝ, DirDeriv f x d =
        GammaHat (fun u v => DirDeriv f x (fun w => (CharVec v w - CharVec u w : ℝ))) d)) ∧
    (∀ f : (V → ℤ) → WithTop ℝ, MExchangeAxiom f → ∀ x ∈ DomZ f,
      TriangleInequality (fun u v => f (fun w => x w - CharVec u w + CharVec v w) - f x) ∧
      SubDifferential f x =
        AdmissiblePotentials (fun u v => f (fun w => x w - CharVec u w + CharVec v w) - f x) ∧
      (SubDifferential f x).Nonempty) := by sorry

end DiscreteConvex.MConvexFunctionsD
