-- Prove2me | Theorems.Thm_FoundationsML_RademacherVC_massart_lemma
-- name    : FoundationsML.RademacherVC.massart_lemma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T21:14:03.33199+00:00
-- url     : https://prove2.me/theorems/8f6e70f5-312f-484e-a7a8-bf23bc49b7f9
-- title:
--   Theorem 3.7 — Massart's lemma
-- statement:
--   **Statement (Theorem 3.7, p. 35, PDF p. 52).** Let $A\subseteq\mathbb R^m$ be a finite set,
--   with $r=\max_{x\in A}\|x\|_2$. Then
--   $$\mathbb E_\sigma\Big[\frac1m\sup_{x\in A}\sum_{i=1}^m\sigma_i x_i\Big] \le r\sqrt{\frac{2\log|A|}{m}},$$
--   where $\sigma_1,\dots,\sigma_m$ are independent uniform $\{-1,+1\}$-valued random
--   variables and $x_1,\dots,x_m$ are the components of vector $x$.
--
--   This is a purely combinatorial, deterministic bound on the expectation of a maximum of
--   linear functionals over a finite set, the key tool relating Rademacher complexity to the
--   growth function (Corollary 3.8).
--
--   **Formalization Note.** `σ` ranges over `Fin m → Bool` as in `EmpiricalRademacherComplexity`
--   (the exact finite uniform average, no measure theory); `A.sup'` needs `A` nonempty
--   (`hA`), matching the book's own implicit assumption that `sup_{x∈A}` is meaningful for a
--   finite set. No `δ` or sample `S` appears — this is deterministic, not probabilistic, over
--   `S` (per `BRIEF.md`'s pitfall note).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 35, Theorem 3.7 (PDF p. 52)

import Mathlib

namespace FoundationsML.RademacherVC

/-- Theorem 3.7 (Massart's lemma; Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, p. 35, PDF p. 52). Let `A ⊆ ℝ^m` be a finite (nonempty)
set, with `r = max_{x∈A} ‖x‖₂`. Then
`E_σ[(1/m) sup_{x∈A} ∑_{i=1}^m σ_i x_i] ≤ r sqrt(2 log|A|/m)`,
where `σ_1,…,σ_m` are independent uniform `{−1,+1}`-valued random variables and
`x_1,…,x_m` are the components of vector `x`.

**Formalization Note.** As in `EmpiricalRademacherComplexity`, `σ` ranges over `Fin m → Bool`
and the expectation over `σ` is the exact finite uniform average over its `2^m` outcomes;
`A.sup'` needs `A` nonempty, matching the book's own implicit assumption that `sup_{x∈A}` is
meaningful for a finite set `A`. -/
theorem massart_lemma
    {m : ℕ} (A : Finset (Fin m → ℝ)) (hA : A.Nonempty) (r : ℝ)
    (hr : ∀ x ∈ A, Real.sqrt (∑ i, (x i) ^ 2) ≤ r) :
    (1 / (2 : ℝ) ^ m) * ∑ σ : Fin m → Bool,
        (1 / (m : ℝ)) * A.sup' hA (fun x => ∑ i : Fin m, (if σ i then (1 : ℝ) else -1) * x i)
      ≤ r * Real.sqrt (2 * Real.log (A.card : ℝ) / m) := by sorry

end FoundationsML.RademacherVC
