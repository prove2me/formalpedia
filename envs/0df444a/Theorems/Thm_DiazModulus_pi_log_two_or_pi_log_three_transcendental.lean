-- Prove2me | Theorems.Thm_DiazModulus_pi_log_two_or_pi_log_three_transcendental
-- name    : DiazModulus.pi_log_two_or_pi_log_three_transcendental
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T16:20:15.930626+00:00
-- url     : https://prove2.me/theorems/aea2ed12-cabc-4281-a6b7-522c689aa0f1
-- title:
--   At least one of π log 2 and π log 3 is transcendental
-- statement:
--   **$\pi\log2$ or $\pi\log3$.**
--
--   At least one of the two real numbers
--
--   $$\pi\log 2 \qquad\text{and}\qquad \pi\log 3$$
--
--   is transcendental.
--
--   Whether $\pi\log2$ alone is transcendental is not known; it is not even known to be irrational (M. Waldschmidt lists $\pi\log2$ and $(\log2)(\log3)$ among such numbers in his 2014 survey of Schanuel's conjecture for the Colloquium De Giorgi). It is a product of two $\mathbb{Q}$-linearly independent logarithms of algebraic numbers, $\pi\log2 = -i\,(i\pi)(\log2)$, both lying on the coordinate axes. When exactly one of the two factors lies on an axis the product is known to be transcendental (G. Diaz, J. Théor. Nombres Bordeaux **16** (2004), Théorème 3, from Roy's strong six exponentials theorem). The disjunction is an instance of `DiazModulus.recip_pi_log_rational_line`. With $\gamma = i\pi\log\alpha$ one has $\mathrm{e}^{\gamma/(i\pi)} = \alpha$. So the positive algebraic $\alpha \neq 1$ for which $\pi\log\alpha$ is algebraic — the exceptions to the imaginary half of (S) — all have rationally proportional logarithms, and $\log2/\log3$ is irrational.
--
--   **Novelty.** None: the ratio of $\pi\log3$ to $\pi\log2$ is $\log 3/\log 2$, which is transcendental by the Gelfond–Schneider theorem, so the two numbers cannot both be algebraic. The contribution of this node is the formal proof.
-- source:
--   Classical consequence of the Gelfond-Schneider theorem (the transcendence of log 3/log 2): A. O. Gelfond (1934) and Th. Schneider (1934); formal proof of Gelfond-Schneider by M. Karatarakis and F. Wiedijk, arXiv:2603.24823. Formal proof: Diaz modulus mission, 23 September 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem pi_log_two_or_pi_log_three_transcendental :
    Transcendental ℚ (Real.pi * Real.log 2) ∨ Transcendental ℚ (Real.pi * Real.log 3) := by sorry

end DiazModulus
