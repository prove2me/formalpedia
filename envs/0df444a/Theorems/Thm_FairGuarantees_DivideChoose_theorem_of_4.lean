-- Prove2me | Theorems.Thm_FairGuarantees_DivideChoose_theorem_of_4
-- name    : FairGuarantees.DivideChoose.theorem_of_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:57.766154+00:00
-- url     : https://prove2.me/theorems/47a020d2-22d9-4560-82b1-08091f91330e
-- title:
--   Theorem of [4] (Avvakumov–Karasev), proof of Lemma 1, p. 10 — every continuous f on subintervals of [0,1] has an n-equipartition
-- statement:
--   Let $f$ be a real-valued function on the intervals $[a,b]\subseteq[0,1]$, $0\le a\le b\le1$, continuous in $(a,b)$ and with $f(a,a)=0$ for all $a\in[0,1]$. Then for every $n\ge1$ there are points
--   $$0=x_0\le x_1\le\dots\le x_n=1$$
--   such that $f(x_{i-1},x_i)$ is the same for $i=1,\dots,n$.
--
--   No sign or monotonicity is assumed on $f$. The paper uses this result of Avvakumov and Karasev to build equipartitions of any share for any utility in $\mathcal D(\Omega)$ (Lemma 1).
--
--   **Formalization Note** $f$ is a function `ℝ → ℝ → ℝ`, continuous on the triangle $\{0\le a\le b\le1\}$; its values elsewhere play no role. The subintervals may be degenerate, as on the page ("subintervals").
-- source:
--   Bogomolnaia & Moulin, Guarantees in Fair Division, arXiv:1911.10009v3, p. 10, §3.2, proof of Lemma 1, first paragraph (the Theorem in [4]: Avvakumov & Karasev, Equipartition of a segment)

import Mathlib

namespace FairGuarantees.DivideChoose

/-- The Theorem of [4] (Avvakumov–Karasev), quoted in the proof of Lemma 1, p. 10: a real
function `f(a, b)` on the intervals `[a, b] ⊆ [0, 1]`, continuous and vanishing on degenerate
intervals, admits for every `n ≥ 1` a division `0 = x₀ ≤ x₁ ≤ ⋯ ≤ xₙ = 1` of `[0, 1]` into
`n` consecutive (possibly degenerate) subintervals on which `f` takes the same value. -/
theorem theorem_of_4 (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) {p | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1})
    (h0 : ∀ a ∈ Set.Icc (0 : ℝ) 1, f a a = 0) (n : ℕ) (hn : 1 ≤ n) :
    ∃ x : Fin (n + 1) → ℝ, x 0 = 0 ∧ x (Fin.last n) = 1 ∧ Monotone x ∧
      ∀ i j : Fin n, f (x i.castSucc) (x i.succ) = f (x j.castSucc) (x j.succ) := by sorry

end FairGuarantees.DivideChoose
