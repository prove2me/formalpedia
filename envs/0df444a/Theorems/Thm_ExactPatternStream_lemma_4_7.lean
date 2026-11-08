-- Prove2me | Theorems.Thm_ExactPatternStream_lemma_4_7
-- name    : ExactPatternStream.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:04:10.053207+00:00
-- url     : https://prove2.me/theorems/0d4db2c7-1c63-4022-8a86-493c8cee756d
-- title:
--   Lemma 4.7 — equal fragments after active triggers pad identically
-- statement:
--   For $r\in\{1,2\}$ let $(S_r,A_r)$ be annotated strings, $u\ne v$, $c>0$, $\#$ fresh, and let $(S_r',A_r')=\mathrm{Pad}(S_r,A_r,u^c\circ v,\#)$ with position maps $\rho_r$. Suppose $c+1\le x_r\le y_r\le|S_r|$, that $(S_1,A_1)[x_1\,.\,.\,y_1)=(S_2,A_2)[x_2\,.\,.\,y_2)$, and that $S_r[x_r-c-1\,.\,.\,x_r)=u^c\circ v$ with $A_r[x_r-c-1]=1$ for both $r$. Then, with $x_r'=\rho_r(x_r)$, $y_r'=\rho_r(y_r)$,
--   $$S_1'[x_1'\,.\,.\,y_1')=S_2'[x_2'\,.\,.\,y_2'),\qquad A_1'[x_1'\,.\,.\,y_1']=A_2'[x_2'\,.\,.\,y_2'].$$
--   The padding of a fragment that starts just after an active trigger depends only on the fragment, which is what keeps pattern and text parses synchronized.
--
--   Differences from the source: none.
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 4.7, p.8 (PDF 9)

import Mathlib
import Definitions.Def_ExactPatternStream_Strings
import Definitions.Def_ExactPatternStream_Pad

namespace ExactPatternStream

/-- Gawrychowski, Janczewski, Jin, Nelson, *An Improved Streaming Algorithm for Exact Pattern Matching* (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 4.7, p.8 (PDF 9).

Equal annotated fragments, each beginning immediately after an active trigger, are padded identically.

**Formalization Note.** `u ≠ v`, `c > 0`, `# ∉ Σ` and `|A_r| = |S_r| + 1` are the conditions of the setup of Definitions 4.1 and 4.3. `(S₁, A₁)[x₁ . . y₁) = (S₂, A₂)[x₂ . . y₂)` is the two slice equalities, and `A'[x' . . y']` is closed, so it includes position `y'`. -/
theorem lemma_4_7 {α : Type*} [DecidableEq α] (S₁ S₂ : List α) (A₁ A₂ : List Bool) (u v hash : α) (c : ℕ)
    (huv : u ≠ v) (hc : 0 < c) (hS₁ : hash ∉ S₁) (hS₂ : hash ∉ S₂)
    (hA₁ : A₁.length = S₁.length + 1) (hA₂ : A₂.length = S₂.length + 1)
    (x₁ y₁ x₂ y₂ : ℕ) (hx₁ : c + 1 ≤ x₁) (hxy₁ : x₁ ≤ y₁) (hy₁ : y₁ ≤ S₁.length)
    (hx₂ : c + 1 ≤ x₂) (hxy₂ : x₂ ≤ y₂) (hy₂ : y₂ ≤ S₂.length)
    (hS : slice S₁ x₁ y₁ = slice S₂ x₂ y₂) (hA : slice A₁ x₁ y₁ = slice A₂ x₂ y₂)
    (ht₁ : slice S₁ (x₁ - c - 1) x₁ = List.replicate c u ++ [v])
    (ht₂ : slice S₂ (x₂ - c - 1) x₂ = List.replicate c u ++ [v])
    (ha₁ : A₁.getD (x₁ - c - 1) false = true) (ha₂ : A₂.getD (x₂ - c - 1) false = true) :
    let r₁ := pad S₁ A₁ u c v hash
    let r₂ := pad S₂ A₂ u c v hash
    let ρ₁ := padRho S₁ A₁ u c v
    let ρ₂ := padRho S₂ A₂ u c v
    slice r₁.1 (ρ₁ x₁) (ρ₁ y₁) = slice r₂.1 (ρ₂ x₂) (ρ₂ y₂) ∧
      slice r₁.2 (ρ₁ x₁) (ρ₁ y₁ + 1) = slice r₂.2 (ρ₂ x₂) (ρ₂ y₂ + 1) := by sorry

end ExactPatternStream
