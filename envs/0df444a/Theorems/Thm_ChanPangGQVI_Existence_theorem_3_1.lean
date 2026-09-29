-- Prove2me | Theorems.Thm_ChanPangGQVI_Existence_theorem_3_1
-- name    : ChanPangGQVI.Existence.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:37:29.339024+00:00
-- url     : https://prove2.me/theorems/9c763767-391b-484b-96de-95764368994e
-- title:
--   Theorem 3.1 — a maximiser of a quasi-concave φ over V(u*) with a set-valued parameter w* ∈ f(u*)
-- statement:
--   Let $\varphi:\mathbb R^n\times\mathbb R^n\times\mathbb R^n\to\mathbb R$ be continuous, let $f$ and $K$ be point-to-set mappings of $\mathbb R^n$ into itself, and let $C$ be a nonempty convex compact subset of $\mathbb R^n$. Suppose that
--
--   1. for each fixed $(u,w)$, the function $v\mapsto \varphi(v,u,w)$ is quasi-concave on $C$;
--   2. $f$ is a nonempty, contractible, compact valued, upper semicontinuous mapping on $C$;
--   3. $V(x)=K(x)\cap C$ is a nonempty, continuous (upper and lower semicontinuous), convex valued mapping on $C$ with closed values.
--
--   Then there exist vectors $u^*\in V(u^*)$ and $w^*\in f(u^*)$ such that
--
--   $$
--   \varphi(v,u^*,w^*)\ \le\ \varphi(u^*,u^*,w^*)\qquad\text{for all } v\in V(u^*).
--   $$
--
--   This is the paper's basic existence result, from which the existence theorem for the GQVI (Theorem 3.2) follows with $\varphi(v,u,w)=-(v-u)^T w$.
--
--   **Formalization Note** Semicontinuity on $C$ is Mathlib's `UpperHemicontinuousOn`/`LowerHemicontinuousOn` with neighbourhoods relative to $C$. The paper cites Berge for semicontinuity, whose upper semicontinuous mappings have compact values; the closedness of $V(x)$ is therefore stated explicitly (without it the theorem fails, e.g. $K(x)\equiv(0,1)$, $C=[0,1]$). The relation in the printed conclusion is illegible in the scan and is read as $\le$, as the proof (which takes $u^*$ as a maximiser) requires.
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 214, Theorem 3.1

import Mathlib
import Definitions.Def_ChanPangGQVI_Existence_IsContractibleSet

open scoped RealInnerProductSpace

namespace ChanPangGQVI.Existence

/-- Chan and Pang 1982, p. 214, Theorem 3.1. Let `φ : ℝⁿ × ℝⁿ × ℝⁿ → ℝ` be continuous, `f`, `K`
point-to-set mappings of `ℝⁿ`, and `C` a nonempty convex compact set such that
(i) for each fixed `(u, w)`, `φ(v, u, w)` is quasi-concave in `v ∈ C`;
(ii) `f` is a nonempty contractible compact valued upper semicontinuous mapping on `C`;
(iii) `V(x) = K(x) ∩ C` is a nonempty continuous convex valued mapping on `C`.
Then there exist `u* ∈ V(u*)` and `w* ∈ f(u*)` with `φ(v, u*, w*) ≤ φ(u*, u*, w*)` for all
`v ∈ V(u*)`.

Implicit hypothesis made explicit: `V(x)` is closed for `x ∈ C` (`hV_closed`). The paper takes its
semicontinuity from Berge, whose upper semicontinuous mappings have compact values; without it the
theorem fails (`K ≡ (0, 1)`, `C = [0, 1]`). "Continuous on `C`" is upper and lower
hemicontinuity with neighbourhoods relative to `C`. The relation in the conclusion is illegible in
the scan and read as `≤` (the proof takes `u*` as a maximiser of `φ(·, u*, w*)` over `V(u*)`). -/
theorem theorem_3_1 {n : ℕ}
    (φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : Continuous (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n) => φ p.1 p.2.1 p.2.2))
    (f K : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC_ne : C.Nonempty) (hC_conv : Convex ℝ C) (hC_cpt : IsCompact C)
    (h_qc : ∀ u w : EuclideanSpace ℝ (Fin n), QuasiconcaveOn ℝ C (fun v => φ v u w))
    (hf_ne : ∀ x ∈ C, (f x).Nonempty) (hf_contr : ∀ x ∈ C, IsContractibleSet (f x))
    (hf_cpt : ∀ x ∈ C, IsCompact (f x)) (hf_usc : UpperHemicontinuousOn f C)
    (hV_ne : ∀ x ∈ C, (K x ∩ C).Nonempty)
    (hV_usc : UpperHemicontinuousOn (fun x => K x ∩ C) C)
    (hV_lsc : LowerHemicontinuousOn (fun x => K x ∩ C) C)
    (hV_conv : ∀ x ∈ C, Convex ℝ (K x ∩ C))
    (hV_closed : ∀ x ∈ C, IsClosed (K x ∩ C)) :
    ∃ u w : EuclideanSpace ℝ (Fin n),
      u ∈ K u ∩ C ∧ w ∈ f u ∧ ∀ v ∈ K u ∩ C, φ v u w ≤ φ u u w := by sorry

end ChanPangGQVI.Existence
