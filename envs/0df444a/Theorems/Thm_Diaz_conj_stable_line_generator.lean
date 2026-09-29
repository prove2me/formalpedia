-- Prove2me | Theorems.Thm_Diaz_conj_stable_line_generator
-- name    : Diaz.conj_stable_line_generator
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:17:53.684069+00:00
-- url     : https://prove2.me/theorems/feeaa74b-417a-4deb-9286-25bddcaee90e
-- title:
--   A conjugation-stable rational line has a real or imaginary generator
-- statement:
--   Let $y \in \mathbb{C}$ be irrational (not a rational number), and suppose $\bar y = a + b y$ with $a, b \in \mathbb{Q}$. Then either $b = 1$, $a = 0$ and $y$ is real, or $b = -1$ and $y - a/2$ is purely imaginary.
--
--   **Where this sits.** This is the normalisation step in the proof of Carlo Perassi's theorem on common logarithmic multipliers: "If $K_u \neq \mathbb{Q}$, write $K_u = \mathbb{Q} \oplus \mathbb{Q}y_1$. From $\bar y_1 = a + b y_1$, conjugation gives $b^{2} = 1$ and $a(1+b) = 0$. For $b = 1$, take the real generator $y_0 = y_1$; for $b = -1$, the generator $y_0 = y_1 - a/2$ is purely imaginary." The hypothesis that $y$ is irrational is what the $\mathbb{Q}$-independence of $1$ and $y_1$ supplies.
--
--   **Proof.** Applying conjugation twice gives $y = a + b(a + by)$, that is $(b+1)\bigl((1-b)y - a\bigr) = 0$. If $b \neq \pm 1$ this makes $y = a/(1-b)$ rational. For $b = 1$ the same relation forces $2a = 0$, so $\bar y = y$. For $b = -1$ it is vacuous, and $\overline{y - a/2} = a - y - a/2 = -(y - a/2)$.
--
--   **What is deliberately not claimed.** The substance of that theorem — that $\dim_{\mathbb{Q}} K_u \le 2$, that $K_u \cap \widetilde{\mathcal{L}} = \mathbb{Q}$, and that every $y \in K_u \setminus \mathbb{Q}$ gives $\operatorname{trdeg}_{\mathbb{Q}}\mathbb{Q}(u,y) = 2$ — uses the six exponentials theorem, Diaz's Theorem 3(1) and Waldschmidt's $2 \times 2$ transcendence-degree estimate, none of which is available in Mathlib. Only the shape of the generator is recorded here.
--
--   Elementary. Novelty is not asserted.
--
--   **Source.** Carlo Perassi, unpublished apart from this node. The mathematics is his; this node only records one step of it in Lean, and claims no novelty of its own.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.conj_stable_line_generator {y : ℂ} (hy : ∀ q : ℚ, y ≠ (q : ℂ)) {a b : ℚ}
    (h : conj y = (a : ℂ) + (b : ℂ) * y) :
    (b = 1 ∧ a = 0 ∧ conj y = y)
      ∨ (b = -1 ∧ conj (y - (a : ℂ) / 2) = -(y - (a : ℂ) / 2)) := by sorry
