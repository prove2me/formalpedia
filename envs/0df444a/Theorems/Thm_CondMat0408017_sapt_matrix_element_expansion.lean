-- Prove2me | Theorems.Thm_CondMat0408017_sapt_matrix_element_expansion
-- name    : CondMat0408017.sapt_matrix_element_expansion
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:20:57.761985+00:00
-- url     : https://prove2.me/theorems/074537e9-3376-42b3-9e57-f9f3b48ea6e2
-- title:
--   Eqs. (83)-(84): expansion of $I(\gamma|q)$ and of the RRE matrix elements in powers of the surface profile
-- statement:
--   Let $\zeta$ be continuous and let the surface have length $L>0$, with $I(\gamma|Q)=\int_{-L/2}^{L/2}dx_1\,e^{-i\gamma\zeta(x_1)-iQx_1}$ and $\tilde\zeta^{(n)}(Q)=\int_{-L/2}^{L/2}dx_1\,\zeta(x_1)^ne^{-iQx_1}$. Then:
--
--   1. For all complex $\gamma$ and real $Q$ (eq. 83),
--   $$I(\gamma|Q)=\sum_{n=0}^\infty\frac{(-i\gamma)^n}{n!}\tilde\zeta^{(n)}(Q).$$
--   2. For each sign, and all $p,q$ and complex $\alpha(p),\alpha_0(q)$ with $\alpha(p)\mp\alpha_0(q)\ne0$ (eq. 84),
--   $$N^\pm_\nu(p|q)=\sum_{n=0}^\infty\frac{\mathcal N^{\pm(n)}_\nu(p|q)}{n!}\tilde\zeta^{(n)}(p-q),$$
--   with $\mathcal N^{\pm(n)}_p=(-i)^n[\pm pq+\alpha(p)\alpha_0(q)][\alpha(p)\mp\alpha_0(q)]^{n-1}$ and $\mathcal N^{\pm(n)}_s=\pm(-i)^n[\alpha(p)\mp\alpha_0(q)]^{n-1}$ for $n\ge1$. The $n=0$ coefficients are $\pm\frac{pq\pm\alpha(p)\alpha_0(q)}{\alpha(p)\mp\alpha_0(q)}$ and $\pm\frac1{\alpha(p)\mp\alpha_0(q)}$.
--   3. On the diagonal, if $\alpha(p)^2=\varepsilon w^2-p^2$, $\alpha_0(p)^2=w^2-p^2$, $\varepsilon\ne1$ and $w\ne0$, then
--   $$\mathcal N^{\pm(0)}_p(p|p)=\frac{\varepsilon\alpha_0(p)\pm\alpha(p)}{\varepsilon-1},\qquad \mathcal N^{\pm(0)}_s(p|p)=\frac{\alpha_0(p)\pm\alpha(p)}{w^2(\varepsilon-1)} .$$
--
--   **Formalization Note** The paper integrates over the whole line. There $\tilde\zeta^{(0)}=2\pi\delta$ and $I$ are distributions, so the expansion is stated for a surface of finite length $L$, where all integrals converge. The paper gives the $n=0$ coefficients only on the diagonal $p=q$, where $\tilde\zeta^{(0)}(p-q)=2\pi\delta(p-q)$ is supported. Here the $n=0$ term is defined for all $(p,q)$, and item 3 checks the paper's diagonal values. The recurrence relation (85), obtained by "equating terms of the same order", is not part of this statement (see the report).
-- source:
--   I. Simonsen, A random walk through surface scattering phenomena: Theory and phenomenology, arXiv:cond-mat/0408017v1 (2004), claim c012 (expansion part); Sec. III.F, eqs. (Theory:int-expansion), (Eq:Theorey:SMPT:N-expansion) [(83)-(84)], PDF p. 27

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex

namespace CondMat0408017

theorem sapt_matrix_element_expansion (ζ : ℝ → ℝ) (hζ : Continuous ζ) (L : ℝ) (hL : 0 < L) :
    (∀ (γ : ℂ) (Q : ℝ),
      HasSum (fun n : ℕ => (-I * γ) ^ n / (n.factorial : ℂ) * zetaPowFT ζ L n Q)
        (zetaIntL ζ L γ Q)) ∧
    (∀ sgn : ℂ, (sgn = 1 ∨ sgn = -1) → ∀ (p q : ℝ) (a a0 : ℂ), a - sgn * a0 ≠ 0 →
      HasSum (fun n : ℕ => rreNpCoeff sgn n p q a a0 / (n.factorial : ℂ) * zetaPowFT ζ L n (p - q))
          (rreNp sgn p q a a0 * zetaIntL ζ L (a - sgn * a0) (p - q)) ∧
        HasSum (fun n : ℕ => rreNsCoeff sgn n a a0 / (n.factorial : ℂ) * zetaPowFT ζ L n (p - q))
          (rreNs sgn a a0 * zetaIntL ζ L (a - sgn * a0) (p - q))) ∧
    (∀ (sgn eps : ℂ) (wv p : ℝ) (a a0 : ℂ), (sgn = 1 ∨ sgn = -1) →
      a ^ 2 = eps * wv ^ 2 - p ^ 2 → a0 ^ 2 = wv ^ 2 - p ^ 2 → eps ≠ 1 → wv ≠ 0 →
      rreNpCoeff sgn 0 p p a a0 = (eps * a0 + sgn * a) / (eps - 1) ∧
        rreNsCoeff sgn 0 a a0 = (a0 + sgn * a) / ((wv : ℂ) ^ 2 * (eps - 1))) := by sorry

end CondMat0408017
