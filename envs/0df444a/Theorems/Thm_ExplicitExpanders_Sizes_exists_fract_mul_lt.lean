-- Prove2me | Theorems.Thm_ExplicitExpanders_Sizes_exists_fract_mul_lt
-- name    : ExplicitExpanders.Sizes.exists_fract_mul_lt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T06:13:08.061992+00:00
-- url     : https://prove2.me/theorems/6aa0bce4-7e95-4c1a-a6ee-cfe996064d51
-- title:
--   Proof of Lemma 2.2 — for irrational $\alpha$ and $\delta>0$ some $k_1\ge1$ has $0<k_1\alpha \bmod 1<\delta$
-- statement:
--   Let $\alpha$ be an irrational real number and let $\delta>0$. Then there is a positive integer $k_1$ such that
--
--   $$
--   0<\{k_1\alpha\}<\delta,
--   $$
--
--   where $\{x\}=x-\lfloor x\rfloor\in[0,1)$ denotes the fractional part, i.e. $x \bmod 1$.
--
--   This is the second sentence of the proof of Lemma 2.2, where it is applied to $\alpha=\log q_1/\log q_2$. The paper notes that it is a special case of the equidistribution theorem which follows easily from the pigeonhole principle. It produces a power $q_1^{k_1}$ that exceeds a power of $q_2$ by a factor of at most $q_2^{\delta}$.
--
--   **Formalization Note** The statement is made for an arbitrary irrational $\alpha$, which is how the paper invokes it ("by the equidistribution theorem"); the application to $\alpha=\log q_1/\log q_2$ is the next milestone. The paper says "an integer $k_1$"; here $k_1$ is a natural number with $k_1\ge1$. The lower bound $0<\{k_1\alpha\}$ already excludes $k_1=0$, and positivity of $k_1$ is what the rest of the proof uses. The fractional part is `Int.fract`.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 7, proof of Lemma 2.2 (second sentence)

import Mathlib

namespace ExplicitExpanders.Sizes

/-- Proof of Lemma 2.2 (arXiv:2003.11673v1, p. 7), second sentence (the pigeonhole special case of
the equidistribution theorem): for an irrational real `α` and every `δ > 0` there is a positive
integer `k₁` with `0 < k₁ α mod 1 < δ`. -/
theorem exists_fract_mul_lt {α : ℝ} (hα : Irrational α) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k₁ : ℕ, 0 < k₁ ∧ 0 < Int.fract ((k₁ : ℝ) * α) ∧ Int.fract ((k₁ : ℝ) * α) < δ := by sorry

end ExplicitExpanders.Sizes
