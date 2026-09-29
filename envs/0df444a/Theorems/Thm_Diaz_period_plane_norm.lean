-- Prove2me | Theorems.Thm_Diaz_period_plane_norm
-- name    : Diaz.period_plane_norm
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:05:22.989974+00:00
-- url     : https://prove2.me/theorems/6319618f-99c9-4744-b0e4-af513e58f4af
-- title:
--   The norm of a point of the period plane of a candidate
-- statement:
--   **Source.** This is Carlo Perassi's mathematics: the norm identity in the proof of his classification of the period plane, unpublished apart from this node. Its case $a=1$, $b=0$ is the identity in the proof of Theorem 3.3 of his companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9), and Appendix A of the note names this node as the identity from which Corollary 3.4 there follows. Published on his mission with his permission. No novelty is claimed for it here; the identity is elementary.
--
--   **Statement.** For $u \in \mathbb{C}$, real $a,b,c$ and $w = a u + b \bar u + 2\pi i c$, writing $\rho = u \bar u$ and $\theta = \Im u$,
--   $$w \bar w  =  (a+b)^2 \rho  +  4\,(a\theta + \pi c)(\pi c - b\theta).$$
--
--   **What it is for.** The period plane of a candidate is $V_u = \mathbb{Q}u + \mathbb{Q}\bar u + \mathbb{Q}\,2\pi i$. Since $\rho \in \overline{\mathbb{Q}}$ for a candidate, this identity turns the question "which points of $V_u$ are again candidates?" into the single algebraic condition $(a\theta + \pi c)(\pi c - b\theta) \in \overline{\mathbb{Q}}$, i.e. membership of $(-ab,\ c(a-b),\ c^2)$ in the relation space $Z(u) = \{\lambda : \lambda_1\theta^2 + \lambda_2\pi\theta + \lambda_3\pi^2 \in \overline{\mathbb{Q}}\}$. The classification into at most four $\mathbb{Q}^\times$-rays is read off from $\dim_{\mathbb{Q}} Z(u) \leq 1$; that dimension count uses Hermite–Lindemann and Lindemann and is not part of this node. The identity itself is unconditional and holds for arbitrary real $a,b,c$.
--
--   **Reading the Lean.** `Complex.normSq z` is $z\bar z$, viewed as a real number; the statement is therefore an identity in $\mathbb{R}$.
--
--   **Proof.** Write $u = x + i\theta$. Then $w = (a+b)x + i[(a-b)\theta + 2\pi c]$, so $w\bar w = (a+b)^2 x^2 + ((a-b)\theta + 2\pi c)^2$; expanding the right-hand side with $\rho = x^2 + \theta^2$ gives the same polynomial.

import Mathlib

open ComplexConjugate

theorem Diaz.period_plane_norm (u : ℂ) (a b c : ℝ) :
    Complex.normSq ((a : ℂ) * u + (b : ℂ) * conj u + 2 * (Real.pi : ℂ) * (c : ℂ) * Complex.I)
      = (a + b) ^ 2 * Complex.normSq u
        + 4 * (a * u.im + Real.pi * c) * (Real.pi * c - b * u.im) := by sorry
