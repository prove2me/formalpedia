-- Prove2me | Theorems.Thm_Arxiv1303_0923_lemma7_source_fields_finitely_many_zeros
-- name    : Arxiv1303_0923.lemma7_source_fields_finitely_many_zeros
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:34:12.519239+00:00
-- url     : https://prove2.me/theorems/3d2f1af1-effd-43c6-9686-10f9f2aea567
-- title:
--   Lemma 7: the total and scattered fields of the distributed source have finitely many zeros in $\mathbb{C}_+$
-- statement:
--   Assume the standing setting of Section 1: bounded domains $\Omega\subset G_1\subset G$ in $\mathbb{R}^3$, $G_1$ convex with $C^1$ boundary $S$, and $\varepsilon\in(0,1)$ with $\operatorname{dist}(S,\partial G)>2\varepsilon$, $\operatorname{dist}(S,\partial\Omega)>2\varepsilon$. Let $q$ satisfy (3), (4) with $m=4$, let $g$ satisfy (13), (14), and for real $k$ let $v(\cdot,k)$ be the solution of (15)-(17). Then:
--
--   1. for every $x\in\overline{G_1}$, the analytic continuation of $k\mapsto v(x,k)$ has at most finitely many zeros in $\mathbb{C}_+$;
--   2. if $x'\in\overline{G_1}$ and $q(x')\neq0$, the analytic continuation of $k\mapsto v_s(x',k)=v(x',k)-v_0(x',k)$ has at most finitely many zeros in $\mathbb{C}_+$.
--
--   These are the counterparts of Lemmas 2 and 3 for the distributed source, used in the proofs of Theorems 3 and 4.
--
--   **Formalization Note** As in Lemma 2, each statement is made for every holomorphic function on some half-plane $\{\operatorname{Im}k>-\gamma\}$, $\gamma>0$, that equals the given function on $\mathbb{R}$.
-- source:
--   M. V. Klibanov, Phaseless inverse scattering problems in 3-d, arXiv:1303.0923v1 (2013), claim c012; Section 5.1, Lemma 7, PDF p. 16

import Mathlib
import Definitions.Def_Arxiv1303_0923_Basic

open MeasureTheory Filter Topology

namespace Arxiv1303_0923

theorem lemma7_source_fields_finitely_many_zeros (geo : Geometry) (q g : R3 → ℝ)
    (hq : IsPotential geo.G 4 q) (hg : IsSourceTerm geo g) (v : R3 → ℝ → ℂ)
    (hv : ∀ k : ℝ, IsSourceSolution q g k (fun x => v x k)) :
    (∀ x ∈ closure geo.G1, ∀ γ : ℝ, 0 < γ → ∀ F : ℂ → ℂ, IsContinuation γ (v x) F →
      {k : ℂ | k ∈ upperHalf ∧ F k = 0}.Finite) ∧
    (∀ x' ∈ closure geo.G1, q x' ≠ 0 → ∀ γ : ℝ, 0 < γ → ∀ F : ℂ → ℂ,
      IsContinuation γ (fun k : ℝ => v x' k - bgField geo.G g x' k) F →
      {k : ℂ | k ∈ upperHalf ∧ F k = 0}.Finite) := by sorry

end Arxiv1303_0923
