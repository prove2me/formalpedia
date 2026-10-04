-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctions_Quasi_quasi_m_minimizer_cut
-- name    : DiscreteConvex.MConvexFunctions.Quasi.quasi_m_minimizer_cut
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:03:30.32299+00:00
-- url     : https://prove2.me/theorems/a5961c64-a0db-4575-b0a7-db8f0acca06f
-- title:
--   Theorem 6.77 -- the quasi M-minimizer cut
-- statement:
--   **Theorem 6.77** (p.174). Let $f : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$ satisfy (SSQM$_{\ne}$), with $\arg\min f \ne \emptyset$. Then the three conclusions of Theorem 6.28 (chunk 06's M-minimizer cut) hold true for $f$, with the M-convex exchange axiom hypothesis there replaced by (SSQM$_{\ne}$) here — the same structural cut certificates, now valid for the strictly larger quasi-convexity class.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.174, Theorem 6.77.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.174, Theorem 6.77

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctions_ArgMin
import Definitions.Def_DiscreteConvex_MConvexFunctions_Quasi_SSQMNeq

open DiscreteConvex.MConvexFunctions

namespace DiscreteConvex.MConvexFunctions.Quasi

/-- Theorem 6.77, the quasi M-minimizer cut (Murota, *Discrete Convex Analysis*, SIAM 2003,
p.174). Let `f : Zⱽ → R ∪ {+∞}` satisfy (SSQM≠), with `arg min f ≠ ∅`. Then the three
conclusions of Theorem 6.28 (chunk `06-mconvex-functions-i`) hold true for `f`, with the
M-convex exchange axiom hypothesis there replaced by (SSQM≠) here. -/
theorem quasi_m_minimizer_cut {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hf : SSQMNeq f) (hne : (ArgMin f).Nonempty) :
    (∀ x ∈ DomZ f, ∀ v u : V,
        (∀ s : V, f (fun w => x w - CharVec u w + CharVec v w) ≤
          f (fun w => x w - CharVec s w + CharVec v w)) →
        ∃ xs ∈ ArgMin f, xs u ≤ x u - 1 + CharVec v u) ∧
    (∀ x ∈ DomZ f, ∀ u v : V,
        (∀ t : V, f (fun w => x w - CharVec u w + CharVec v w) ≤
          f (fun w => x w - CharVec u w + CharVec t w)) →
        ∃ xs ∈ ArgMin f, xs v ≥ x v - CharVec u v + 1) ∧
    (∀ x ∈ DomZ f \ ArgMin f, ∀ u v : V,
        (∀ s t : V, f (fun w => x w - CharVec u w + CharVec v w) ≤
          f (fun w => x w - CharVec s w + CharVec t w)) →
        ∃ xs ∈ ArgMin f, xs u ≤ x u - 1 ∧ xs v ≥ x v + 1) := by sorry

end DiscreteConvex.MConvexFunctions.Quasi
