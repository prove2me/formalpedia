-- Prove2me | Theorems.Thm_FibAnyon_Approx_proposition_4
-- name    : FibAnyon.Approx.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:24.67967+00:00
-- url     : https://prove2.me/theorems/23b58924-01a3-40b0-bed4-4be0c1cafb1e
-- title:
--   Proposition 4, p. 4 — integer Gauss complexity and its three alternatives
-- statement:
--   For $x=a+b\omega+c\omega^2+d\omega^3\in\mathbb Z[\omega]$, the Gauss complexity $G(x)=|x|^2+|x^\bullet|^2$ is an integer. Its possible cases are $G(x)=0$ only when $x=0$, $G(x)=2$ only when $x$ is a power of $\omega$, or $G(x)\ge3$. In addition,
--
--   $$G(x)\le\frac52(a^2+b^2+c^2+d^2).$$
--
--   The integer gap and coefficient bound support the terminating exact-synthesis loop and later complexity estimates.
--
--   **Formalization Note** The exponent for $G(x)=2$ is normalized to one of $0,\ldots,9$, since $\omega^{10}=1$.
-- source:
--   Kliuchnikov, Bocharov, Svore, Asymptotically optimal topological quantum compiling, arXiv:1310.4150v1, p. 4, Proposition 4

import Mathlib
import Definitions.Def_FibAnyon_Approx_Model

noncomputable section

namespace FibAnyon.Approx

/-- Proposition 4, p. 4. -/
theorem proposition_4 (x : ZOmega) :
    (∃ n : ℤ, gaussG x = n) ∧
    (gaussG x = 0 → x = 0) ∧
    (gaussG x = 2 → ∃ k : ℕ, k < 10 ∧ x = ZOmega.w.pow k) ∧
    (gaussG x = 0 ∨ gaussG x = 2 ∨ 3 ≤ gaussG x) ∧
    gaussG x ≤ (5/2 : ℝ) *
      ((x.a:ℝ)^2 + (x.b:ℝ)^2 + (x.c:ℝ)^2 + (x.d:ℝ)^2) := by sorry

end FibAnyon.Approx
