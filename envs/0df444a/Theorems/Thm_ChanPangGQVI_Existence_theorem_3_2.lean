-- Prove2me | Theorems.Thm_ChanPangGQVI_Existence_theorem_3_2
-- name    : ChanPangGQVI.Existence.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:38:22.993524+00:00
-- url     : https://prove2.me/theorems/7f3285dc-5ab6-409c-95cd-a38f51900292
-- title:
--   Theorem 3.2 — existence of a solution of GQVI(K, f) from a compact truncation C = U ∩ E
-- statement:
--   Let $f$ and $K$ be point-to-set mappings of $\mathbb R^n$ into itself. Suppose there are convex sets $U$ and $E$, with $E$ solid, such that
--
--   1. $C=U\cap E$ is a nonempty compact set;
--   2. $f$ is a nonempty, contractible, compact valued, upper semicontinuous mapping on $C$;
--   3. $K$ is convex valued and $K(x)\subseteq U$ for every $x\in C$;
--   4. $V(u)=K(u)\cap C$ is a nonempty, continuous mapping on $C$ with closed values;
--   5. for each vector $u$ with $u\in V(u)$ and $u\in\partial E$ there is $u^0\in K(u)\cap E^0$ with
--   $$
--   \inf_{w\in f(u)}(u-u^0)^T w\ \ge\ 0 .
--   $$
--
--   Then $\mathrm{GQVI}(K,f)$ has a solution: there are $x\in K(x)$ and $y\in f(x)$ with $(x'-x)^T y\ge 0$ for all $x'\in K(x)$.
--
--   Here $E^0$ is the interior and $\partial E$ the boundary of $E$. The theorem is the paper's general existence result; conditions 1–4 give a solution of the problem truncated to $C$, and condition 5 guarantees that it solves the untruncated problem.
--
--   **Formalization Note** The set $E$ is `Es` in Lean. Condition 5 is stated as "$0\le (u-u^0)^T w$ for every $w\in f(u)$", which matches the paper's convention that an infimum over an empty set is $+\infty$; its relation is illegible in the scan and read as $\ge 0$. The closedness of $V(u)$ is Berge's compact-values convention, made explicit.
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 215, Theorem 3.2

import Mathlib
import Definitions.Def_ChanPangGQVI_Existence_GQVI
import Definitions.Def_ChanPangGQVI_Existence_IsContractibleSet

open scoped RealInnerProductSpace

namespace ChanPangGQVI.Existence

/-- Chan and Pang 1982, p. 215, Theorem 3.2. Let `f`, `K` be point-to-set mappings of `ℝⁿ`, and
`U`, `E` convex sets with `E` solid such that
(i) `C = U ∩ E` is nonempty and compact;
(ii) `f` is a nonempty contractible compact valued upper semicontinuous mapping on `C`;
(iii) `K` is convex valued and `K(C) ⊆ U`;
(iv) `V(u) = K(u) ∩ C` is a nonempty continuous mapping on `C`;
(v) for each `u ∈ V(u) ∩ ∂E` there is `u⁰ ∈ K(u) ∩ E°` with `inf_{w ∈ f(u)} (u - u⁰)ᵀ w ≥ 0`.
Then `GQVI(K, f)` has a solution.

Implicit hypothesis made explicit: `V(u)` is closed for `u ∈ C` (`hV_closed`, Berge's compact
values). Condition (v) is written in ∀-form (infimum over `∅` is `∞`); its relation is illegible
in the scan and read as `≥ 0`. The set `E` is named `Es` in Lean. -/
theorem theorem_3_2 {n : ℕ} (f K : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (U Es : Set (EuclideanSpace ℝ (Fin n)))
    (hU : Convex ℝ U) (hEs : Convex ℝ Es) (hEs_solid : (interior Es).Nonempty)
    (hC_ne : (U ∩ Es).Nonempty) (hC_cpt : IsCompact (U ∩ Es))
    (hf_ne : ∀ x ∈ U ∩ Es, (f x).Nonempty) (hf_contr : ∀ x ∈ U ∩ Es, IsContractibleSet (f x))
    (hf_cpt : ∀ x ∈ U ∩ Es, IsCompact (f x)) (hf_usc : UpperHemicontinuousOn f (U ∩ Es))
    (hK_conv : ∀ x, Convex ℝ (K x)) (hKU : ∀ x ∈ U ∩ Es, K x ⊆ U)
    (hV_ne : ∀ u ∈ U ∩ Es, (K u ∩ (U ∩ Es)).Nonempty)
    (hV_usc : UpperHemicontinuousOn (fun u => K u ∩ (U ∩ Es)) (U ∩ Es))
    (hV_lsc : LowerHemicontinuousOn (fun u => K u ∩ (U ∩ Es)) (U ∩ Es))
    (hV_closed : ∀ u ∈ U ∩ Es, IsClosed (K u ∩ (U ∩ Es)))
    (hv : ∀ u ∈ U ∩ Es, u ∈ K u → u ∈ frontier Es →
      ∃ u0 ∈ K u ∩ interior Es, ∀ w ∈ f u, 0 ≤ ⟪u - u0, w⟫) :
    ∃ x y : EuclideanSpace ℝ (Fin n), IsGQVISolution K f x y := by sorry

end ChanPangGQVI.Existence
