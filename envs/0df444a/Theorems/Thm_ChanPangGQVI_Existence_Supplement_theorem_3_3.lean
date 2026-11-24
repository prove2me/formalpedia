-- Prove2me | Theorems.Thm_ChanPangGQVI_Existence_Supplement_theorem_3_3
-- name    : ChanPangGQVI.Existence.Supplement.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:55:01.970822+00:00
-- url     : https://prove2.me/theorems/f008c7d2-e2ee-4710-b35c-f155ab8f887b
-- title:
--   Theorem 3.3 — existence for GQVI(K, f) from a compact truncation C with a domination condition outside C (corrected: C nonempty and convex)
-- statement:
--   Work in $\mathbb R^n$ with the Euclidean inner product. Let $f$ and $K$ be point-to-set mappings of $\mathbb R^n$ into itself. Recall that a solution of the generalized quasi-variational inequality $\mathrm{GQVI}(K,f)$ is a pair $(x,y)$ with $x\in K(x)$, $y\in f(x)$ and $(x'-x)^T y\ge 0$ for all $x'\in K(x)$.
--
--   Let $C\subseteq\mathbb R^n$ be a nonempty convex compact set and write $V(x)=K(x)\cap C$. Assume:
--
--   1. $f$ is a nonempty, contractible, compact valued, upper semicontinuous mapping on $C$;
--   2. $V$ is a nonempty, closed and convex valued, continuous (upper and lower semicontinuous) mapping on $C$;
--   3. for each $x\in C$ and each $z\in K(x)\setminus C$ there is a vector $u\in V(x)$ with
--   $$
--   \inf_{y\in f(x)}\,(z-u)^T y\ \ge\ 0 .
--   $$
--
--   Then $\mathrm{GQVI}(K,f)$ has a solution:
--
--   $$
--   \exists\,x,y\in\mathbb R^n:\quad x\in K(x),\quad y\in f(x),\quad (x'-x)^T y\ge 0\ \ \text{for all } x'\in K(x).
--   $$
--
--   The variational test ranges over all of $K(x)$, not only over $V(x)$; condition 3 is what passes from the problem truncated to $C$ to the full problem. Theorem 3.3 is a companion of Theorem 3.2, with a condition on the points of $K(x)$ outside $C$ in place of a condition on the boundary of a solid set.
--
--   **Formalization Note** Semicontinuity is relative to $C$ (Mathlib's `UpperHemicontinuousOn`/`LowerHemicontinuousOn`). Condition 3 is written as "$(z-u)^T y\ge 0$ for every $y\in f(x)$", which is the infimum condition. Closed values of $V$ are Berge's convention for upper semicontinuous mappings (compact values), which the paper adopts by citation.
--
--   Differences from the source:
--   - correction: "a compact set C" → C nonempty, convex and compact; reason: the proof is "By Theorem 3.1", whose set C is nonempty convex compact. As printed the theorem is false: C = {0, 1} ⊆ ℝ, K(x) = {1} for x ≠ 1, K(1) = {0}, f ≡ {0} satisfies (i)–(iii) ((iii) is vacuous) but no x has x ∈ K(x); C = ∅ with K ≡ ∅ also fails. Excluded cases: empty or nonconvex C.
--   - reading: V upper semicontinuous on C → in addition V(x) closed for x ∈ C; reason: the paper takes semicontinuity from Berge [6], whose upper semicontinuous mappings have compact values; without it the theorem fails (K ≡ (0, 1), C = [0, 1], f ≡ {1}).
--   - encoding: "continuous on C", "upper semicontinuous on C" → upper and lower hemicontinuity relative to C; reason: Berge's definitions with neighbourhoods relative to the domain C; same instances.
--   - encoding: inf_{y∈f(x)} (z − u)^T y ≥ 0 → ∀ y ∈ f(x), 0 ≤ (z − u)^T y; reason: an infimum of reals is ≥ 0 iff every term is (inf ∅ = ∞ by the paper's convention); same instances.
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), pp. 215–216, Theorem 3.3

import Mathlib
import Definitions.Def_ChanPangGQVI_Existence_GQVI
import Definitions.Def_ChanPangGQVI_Existence_IsContractibleSet

open scoped RealInnerProductSpace

namespace ChanPangGQVI.Existence.Supplement

open ChanPangGQVI.Existence

/-- Chan and Pang 1982, pp. 215–216, Theorem 3.3. Let `f`, `K` be point-to-set mappings of `ℝⁿ`
and `C` a compact set such that
(i) `f` is a nonempty contractible compact valued upper semicontinuous mapping on `C`;
(ii) `V(x) = K(x) ∩ C` is a nonempty continuous convex-valued mapping on `C`;
(iii) for each `x ∈ C` and each `z ∈ K(x) \ C` there is `u ∈ V(x)` with
`inf_{y ∈ f(x)} (z - u)ᵀ y ≥ 0`.
Then `GQVI(K, f)` has a solution.

Correction (supported by the proof, which is "By Theorem 3.1"): `C` is also nonempty and convex
(`hC_ne`, `hC_conv`), exactly Theorem 3.1's hypothesis on `C`. As printed the theorem is false
(`C = {0, 1} ⊆ ℝ`, `K(x) = {1}` for `x ≠ 1`, `K(1) = {0}`, `f ≡ {0}`; or `C = ∅`).
Implicit hypothesis made explicit: `V(x)` is closed for `x ∈ C` (`hV_closed`, Berge's compact
values). "Continuous on `C`" is upper and lower hemicontinuity relative to `C`. Condition (iii) is
in ∀-form (the infimum over `f(x)` is `≥ 0` iff every term is). The conclusion is a solution of
the full `GQVI(K, f)`: the test ranges over all of `K(x)`. -/
theorem theorem_3_3 {n : ℕ} (f K : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC_ne : C.Nonempty) (hC_conv : Convex ℝ C) (hC_cpt : IsCompact C)
    (hf_ne : ∀ x ∈ C, (f x).Nonempty) (hf_contr : ∀ x ∈ C, IsContractibleSet (f x))
    (hf_cpt : ∀ x ∈ C, IsCompact (f x)) (hf_usc : UpperHemicontinuousOn f C)
    (hV_ne : ∀ x ∈ C, (K x ∩ C).Nonempty)
    (hV_usc : UpperHemicontinuousOn (fun x => K x ∩ C) C)
    (hV_lsc : LowerHemicontinuousOn (fun x => K x ∩ C) C)
    (hV_conv : ∀ x ∈ C, Convex ℝ (K x ∩ C))
    (hV_closed : ∀ x ∈ C, IsClosed (K x ∩ C))
    (hiii : ∀ x ∈ C, ∀ z ∈ K x \ C, ∃ u ∈ K x ∩ C, ∀ y ∈ f x, 0 ≤ ⟪z - u, y⟫) :
    ∃ x y : EuclideanSpace ℝ (Fin n), IsGQVISolution K f x y := by sorry

end ChanPangGQVI.Existence.Supplement
