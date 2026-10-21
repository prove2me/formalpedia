-- Prove2me | Theorems.Thm_EFXGenVal_TwoVal_lemma_8
-- name    : EFXGenVal.TwoVal.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:55.00518+00:00
-- url     : https://prove2.me/theorems/34a10caa-eaa9-4794-abd1-475ec6e5ee21
-- title:
--   Lemma 8, p. 9 (Berger et al.) — a Pareto improvable cycle yields a Pareto-dominating allocation that keeps EFX (corrected form)
-- statement:
--   Let the agents have normalized, monotone, non-degenerate valuations, and let $X$ be an allocation (not necessarily EFX). Suppose the champion graph $M_X$ contains a Pareto improvable cycle
--   $$a_1\xrightarrow{H_1}a_2\xrightarrow{H_2}\cdots\xrightarrow{H_{k-1}}a_k\xrightarrow{H_k}a_1 .$$
--   Then there is an allocation $Y$ that Pareto dominates $X$ such that
--
--   1. for every agent $j$ not on the cycle and every agent $i$: if $i$ does not EFX envy $j$ in $X$, then $i$ does not EFX envy $j$ in $Y$;
--   2. for every agent $i$ and every vertex $a_t$ of the cycle: if $i$ does not EFX envy the successor $a_{t+1}$ in $X$, then $i$ does not EFX envy $a_t$ in $Y$ (indices mod $k$);
--   3. if $X$ is EFX, then so is $Y$;
--   4. every agent $a_t$ on the cycle is strictly better off: $X_{a_t}<_{a_t}Y_{a_t}$.
--
--   PI cycles are the basic source of progress in the paper: the proof of Theorem 14 applies this lemma both to EFX and to semi-EFX allocations.
--
--   **Formalization Note** The page states the preservation clause as "for any $i,j\in N$, if $i$ does not EFX envy $j$ in $X$, then neither in $Y$". For an allocation $X$ that is not EFX this is false as printed: along the cycle bundles move from $a_{t+1}$ to $a_t$, and a third agent who EFX envied $a_{t+1}$ but not $a_t$ in $X$ can be forced to EFX envy $a_t$ in every admissible $Y$ (a three-agent, four-item non-degenerate instance exists). Berger et al.'s original lemma assumes $X$ EFX. The statement here keeps the page's clause for agents off the cycle and shifts it along the cycle for agents on it. This is what the proof of Theorem 14 uses to keep semi-EFX allocations semi-EFX. The cycle is encoded as in the definition file: distinct vertices, labels `none`/`some g` with $g$ unallocated, and labels of distinct edges disjoint.
-- source:
--   Mahara, Extension of Additive Valuations to General Valuations on the Existence of EFX, arXiv:2107.09901v2, §2.3, Lemma 8, p. 9 (citing Berger et al., (Almost Full) EFX Exists for Four Agents (and Beyond), arXiv:2102.10654, Lemma 3.5)

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting
import Definitions.Def_EFXGenVal_TwoVal_Setting

namespace EFXGenVal.TwoVal

open LittleCharity.EFX

/-- Lemma 8, p. 9 (Berger et al.), corrected form. The page's clause "for any i, j, if i does
not EFX envy j in X, then neither in Y" is false for a non-EFX allocation X; it is kept for
agents `j` off the cycle and shifted along the cycle (`a (t+1)` in `X` to `a t` in `Y`). -/
theorem lemma_8 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : IsNormalized v) (hmono : IsMonotoneVal v) (hnd : IsNonDegenerate v)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X)
    (k : ℕ) (a : Fin k → Fin n) (H : Fin k → Option (Fin m))
    (hC : IsPICycle v X k a H) :
    ∃ Y : Fin n → Finset (Fin m), IsPartialAllocation Y ∧ ParetoDominates v Y X ∧
      (∀ i j, (∀ t, a t ≠ j) → ¬ EFXEnvies v X i j → ¬ EFXEnvies v Y i j) ∧
      (∀ i t, ¬ EFXEnvies v X i (a (finRotate k t)) → ¬ EFXEnvies v Y i (a t)) ∧
      (IsEFX v X → IsEFX v Y) ∧
      ∀ t, v (a t) (X (a t)) < v (a t) (Y (a t)) := by sorry

end EFXGenVal.TwoVal
