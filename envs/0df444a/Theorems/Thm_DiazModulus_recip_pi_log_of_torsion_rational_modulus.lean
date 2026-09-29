-- Prove2me | Theorems.Thm_DiazModulus_recip_pi_log_of_torsion_rational_modulus
-- name    : DiazModulus.recip_pi_log_of_torsion_rational_modulus
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T06:25:28.261589+00:00
-- url     : https://prove2.me/theorems/4ab529e6-b0c9-451a-926e-339e9c2bbfea
-- title:
--   If t² + π² is rational for a real t ≠ 0 with e^t algebraic, then e^{iγ/π} is transcendental for every rational γ ≠ 0
-- statement:
--   Let $t \neq 0$ be a real number with $e^{t}$ algebraic and $t^{2} + \pi^{2} = r \in \mathbb{Q}$. Then
--
--   $$e^{i\gamma/\pi}$$
--
--   is transcendental for every non-zero rational $\gamma$.
--
--   Two open statements meet here. Diaz's conjecture at $t + i\pi$ says that $t^{2} + \pi^{2}$ is transcendental. The statement (S) for real $\gamma$ (`DiazModulus.recip_pi_not_log_real_gamma`, Open) says that $e^{\gamma/(i\pi)} = e^{-i\gamma/\pi}$ is transcendental for every non-zero real algebraic $\gamma$; its smallest case is $e^{i/\pi}$ (compare `DiazModulus.exp_i_div_pi_or_exp_i_pi_cube_transcendental`). The hypothesis here is expected never to hold. What the theorem shows is that the two statements cannot both fail at rational data: a rational value of $t^{2} + \pi^{2}$ forces $e^{i\gamma/\pi}$ to be transcendental at every rational $\gamma \neq 0$.
--
--   **Proof.** By `DiazModulus.diaz_number_forces_transcendence`, $e^{r/(i\pi)} = e^{-ir/\pi}$ is transcendental. If $e^{i\gamma/\pi}$ were algebraic, write $r/\gamma = a/b$ with $a \in \mathbb{Z}$ and $b \geq 1$: then $(e^{ir/\pi})^{b} = (e^{i\gamma/\pi})^{a}$ is algebraic, so $e^{ir/\pi}$ and its inverse $e^{-ir/\pi}$ are algebraic.
--
--   **Novelty.** Not found in the sources read (among them Diaz 2004 and 2007, Roy–Waldschmidt 1995 and 1997, and Waldschmidt 1973, 1974 and 2005). The transcendence of $e^{-ir/\pi}$ is an instance of a classical dichotomy: by M. Waldschmidt, *Nombres transcendants*, Lecture Notes in Math. **402** (1974), p. 202, two $\mathbb{Q}$-independent logarithms $\ell_1, \ell_2$ are either algebraically independent, or $e^{\ell_1^{2}/\ell_2}$ is transcendental; take $\ell_1 = t$ and $\ell_2 = i\pi$. The scaling step is elementary, and `DiazModulus.recip_pi_log_rational_line` proves a stronger form of it.
-- source:
--   Not found in the sources read (among them Diaz 2004 and 2007, Roy–Waldschmidt 1995 and 1997, and Waldschmidt 1973, 1974 and 2005). The key step is an instance of M. Waldschmidt, Nombres transcendants, Lecture Notes in Math. 402, Springer, 1974, p. 202, at the logarithms t and iπ (equivalently M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Corollaire 4, at e^(t+iπ), e^(t−iπ) and e^(iπ)). Statement and formal proof: Diaz modulus mission, 29 September 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

/-- If `t² + π²` is rational for some real `t ≠ 0` with `e^t` algebraic, then `e^{iγ/π}` is
transcendental for every non-zero rational `γ`. -/
theorem recip_pi_log_of_torsion_rational_modulus (t : ℝ) (ht : t ≠ 0)
    (he : IsAlgebraic ℚ (Complex.exp (t : ℂ))) (r : ℚ) (hr : t ^ 2 + Real.pi ^ 2 = r)
    (γ : ℚ) (hγ : γ ≠ 0) :
    Transcendental ℚ (Complex.exp (Complex.I * (γ : ℂ) / ((Real.pi : ℝ) : ℂ))) := by
  sorry

end DiazModulus
