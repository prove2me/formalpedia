-- Prove2me | Theorems.Thm_CGWH_exists_subset_range_of_isCompact_of_isColimit
-- name    : CGWH.exists_subset_range_of_isCompact_of_isColimit
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:43.153322+00:00
-- url     : https://prove2.me/theorems/efc64758-d697-45df-a052-4c7e08fbb609
-- title:
--   A compact subset of a sequential colimit of $T_1$ spaces with finite-fibred structure maps lies in the image of a finite stage
-- statement:
--   Compact subsets of the colimit of a sequence of $T_1$ spaces are contained in a finite stage, provided the canonical maps to the colimit have finite fibres.
--
--   Let
--   $$X_0\longrightarrow X_1\longrightarrow X_2\longrightarrow\cdots$$
--   be a sequence of topological spaces and continuous maps, and let $X=\operatorname{colim}_{n\ge0}X_n$ be its colimit in the category of topological spaces, with canonical continuous maps $f_n:X_n\to X$. Thus $X=\bigcup_nf_n(X_n)$, the images $f_n(X_n)$ increase with $n$, and a subset $U\subseteq X$ is open if and only if $f_n^{-1}(U)$ is open in $X_n$ for every $n$.
--
--   **Statement.** Assume that
--
--   1. every $X_n$ is a $T_1$ space (its points are closed), and
--   2. every $f_n:X_n\to X$ has finite fibres: $f_n^{-1}(\{x\})$ is finite for every $n\ge0$ and every $x\in X$.
--
--   Then for every compact subset $K\subseteq X$ there exists $n\ge0$ such that
--   $$K\subseteq f_n(X_n).$$
--
--   Hypothesis 2 holds in particular when all transition maps $X_n\to X_{n+1}$ are injective, in which case the $f_n$ are injective; this is the situation of an expanding sequence of spaces, and the statement is then the familiar fact that a compact subset of a union $\bigcup_nX_n$ with the colimit topology lies in some $X_n$. The paper uses the lemma to show that a weakly Hausdorff space which is a sequential colimit of compact Hausdorff subspaces is hemicompact, and hence locally compact when it is first-countable (Corollary E.2.1.17).
--
--   **Formalization Note.** The sequence is a functor `F : ℕ ⥤ TopCat.{u}` (`ℕ` with its order, so `F.obj n` is $X_n$), and the colimit is given by an arbitrary colimit cocone: `c : Limits.Cocone F` with `hc : Limits.IsColimit c`, so `c.pt` is $X$ and `c.ι.app n : F.obj n ⟶ c.pt` is $f_n$, used as a function through the coercion of morphisms of `TopCat`. Hypothesis 2 is `((c.ι.app n) ⁻¹' {x}).Finite` for all `n` and `x`; the conclusion is `∃ n, K ⊆ Set.range (c.ι.app n)`. The file imports Mathlib only.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 850, Lemma E.2.1.15; classical reference (as cited by the paper at this place): V. L. Hansen, Some theorems on direct limits of expanding sequences of manifolds, Math. Scand. 29 (1971), 5-36, Lemma 2.4

import Mathlib

open CategoryTheory Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGWH

theorem exists_subset_range_of_isCompact_of_isColimit
    {F : ℕ ⥤ TopCat.{u}} {c : Limits.Cocone F} (hc : Limits.IsColimit c)
    (hT1 : ∀ n : ℕ, T1Space (F.obj n))
    (hfin : ∀ (n : ℕ) (x : c.pt), ((c.ι.app n) ⁻¹' {x}).Finite)
    {K : Set c.pt} (hK : IsCompact K) : ∃ n : ℕ, K ⊆ Set.range (c.ι.app n) := by sorry

end CGWH
