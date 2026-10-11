-- Prove2me | Theorems.Thm_ClosingLemma_closing_lemma_Cr
-- name    : ClosingLemma.closing_lemma_Cr
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T03:16:13.302742+00:00
-- url     : https://prove2.me/theorems/41e83864-779d-4892-a7e7-50ea8d1533ee
-- title:
--   $C^r$ closing lemma for diffeomorphisms ($r \ge 1$)
-- statement:
--   Let $M$ be a closed manifold: a compact Hausdorff smooth manifold without boundary, of dimension $n$. Let $r\ge1$ be an integer, let $f\in\mathrm{Diff}^r(M)$ be a $C^r$ diffeomorphism, and let $p\in\Omega(f)$ be a **nonwandering** point of $f$: for every neighbourhood $U$ of $p$ there is $k\ge1$ with $f^k(U)\cap U\neq\emptyset$. Then $f$ can be $C^r$-approximated by diffeomorphisms for which $p$ is periodic:
--
--   $$\forall\,\mathcal V\ni f\ \text{a neighbourhood in the } C^r \text{ topology of } \mathrm{Diff}^r(M),\qquad \exists\,g\in\mathcal V,\ \exists\,m\ge1:\ g^m(p)=p .$$
--
--   This is the $C^r$ closing lemma. For $r=1$ it is Pugh's closing lemma (1967); for $r\ge2$ it is an open problem (Open Problem Garden; Smale's tenth problem).
--
--   **Formalization Note** $\mathrm{Diff}^r(M)$ is `Diffeomorph (𝓡 n) (𝓡 n) M M r` for a $C^\infty$ manifold modelled on `EuclideanSpace ℝ (Fin n)`; the $C^r$ topology is `ClosingLemma.crTopology r` (weak $C^r$ topology through charts, which on a closed manifold equals the Whitney topology). The nonwandering set is the published `PughClosingLemma.nonwanderingSet`, and "periodic" is membership in Mathlib's `Function.periodicPts` (period at least $1$).
-- source:
--   Open Problem Garden, "Closing Lemma for Diffeomorphism (Dynamical Systems)", posted by Jailton Viana, April 24th, 2013, https://www.openproblemgarden.org/op/closing_lemma_for_diffeomorphism_dynamical_systems (the boxed Conjecture; bibliography: Bonatti–Díaz–Viana, Dynamics beyond uniform hyperbolicity, Encyclopaedia of Mathematical Sciences vol. 102, Springer 2005). Known for r = 1: C. C. Pugh, An improved closing lemma and a general density theorem, Amer. J. Math. 89 (1967), https://doi.org/10.2307/2373414

import Mathlib
import Definitions.Def_PughClosingLemma_nonwandering
import Definitions.Def_ClosingLemma_DiffeoCrTopology

open scoped Manifold ContDiff Topology

namespace ClosingLemma

theorem closing_lemma_Cr {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (r : ℕ) (hr : 1 ≤ r) (f : Diff n M r) (p : M)
    (hp : p ∈ PughClosingLemma.nonwanderingSet f) :
    ∀ V ∈ @nhds (Diff n M r) (crTopology r) f,
      ∃ g ∈ V, p ∈ Function.periodicPts g := by sorry

end ClosingLemma
