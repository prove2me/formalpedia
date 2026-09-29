-- Prove2me | Theorems.Thm_Diaz_order_quantisation
-- name    : Diaz.order_quantisation
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:05:22.209311+00:00
-- url     : https://prove2.me/theorems/e7720fc5-7e26-44ca-bf16-1eba18b99997
-- title:
--   Effective quantisation from the order of $\alpha/\bar\alpha$
-- statement:
--   **Source.** This is Carlo Perassi's mathematics: the sharpening of the quantisation bound stated after Theorem 3.1 of his companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9). Published on his mission with his permission. No novelty is claimed for it here; the argument is elementary.
--
--   **Statement.** Let $\alpha = e^{u}$ and suppose $\xi = \alpha/\bar\alpha$ satisfies $\xi^{m} = 1$ for some $m \geq 1$. If $u$ lies on neither axis, then
--   $$u\bar u  >  \frac{\pi^2}{m^2} .$$
--
--   **A further step.** In its original form, which is unpublished, the corollary goes one step further: if $\alpha$ has degree $d$ then $\xi \in \mathbb{Q}(\alpha,\bar\alpha)$ has degree at most $d^2$, so $\varphi(m) \leq d^2$; the elementary estimate $\varphi(m) \geq \sqrt{m/2}$ then gives $m \leq 2d^4$ and hence $u\bar u > \pi^2/(4d^8)$. That last step needs a lower bound on Euler's totient which is **not available in Mathlib at this revision**, so only the geometric half is stated here; anyone supplying $\varphi(m) \geq \sqrt{m/2}$ can read off the $d^{-8}$ form from this node immediately.
--
--   **Proof.** $\alpha/\bar\alpha = e^{u - \bar u} = e^{2i\Im u}$, so $\xi^m = 1$ says $e^{2 i m \Im u} = 1$, i.e. $m \Im u = n\pi$ for some $n \in \mathbb{Z}$. As $\Im u \neq 0$ we get $n \neq 0$ and $|\Im u| \geq \pi/m$, so $(\Im u)^2 \geq \pi^2/m^2$; adding $(\Re u)^2 > 0$ gives the strict inequality.

import Mathlib

open ComplexConjugate

theorem Diaz.order_quantisation {u : ℂ} {m : ℕ} (hm : 0 < m)
    (hξ : (Complex.exp u / conj (Complex.exp u)) ^ m = 1)
    (hre : u.re ≠ 0) (him : u.im ≠ 0) :
    Real.pi ^ 2 / (m : ℝ) ^ 2 < Complex.normSq u := by sorry
