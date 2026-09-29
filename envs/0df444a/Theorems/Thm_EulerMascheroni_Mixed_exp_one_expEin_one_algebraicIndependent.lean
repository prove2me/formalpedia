-- Prove2me | Theorems.Thm_EulerMascheroni_Mixed_exp_one_expEin_one_algebraicIndependent
-- name    : EulerMascheroni.Mixed.exp_one_expEin_one_algebraicIndependent
-- status  : Open
-- author  : @shivm
-- created : 2026-09-25T22:41:59.27599+00:00
-- url     : https://prove2.me/theorems/be444f9a-2bc2-40c6-8d50-575c683c6b39
-- title:
--   $e$ and $e\,\mathrm{Ein}(1) = e\gamma+\delta$ are algebraically independent
-- statement:
--   Let $e = \exp(1)$ and let
--   $$\operatorname{Ein}(z) = \sum_{n\ge 0} \frac{(-1)^n z^{n+1}}{(n+1)\,(n+1)!} = \int_0^z \frac{1-e^{-t}}{t}\,dt$$
--   be the entire complementary exponential integral, so that $\theta := e\cdot\operatorname{Ein}(1) = \texttt{expEin}(1)$.
--
--   **Theorem.** The numbers $e$ and $\theta = e\,\operatorname{Ein}(1)$ are algebraically independent over $\mathbb{Q}$: if $P \in \mathbb{Q}[X,Y]$ satisfies $P(e,\theta)=0$, then $P=0$.
--
--   By Hardy's identity $\operatorname{Ein}(1) = \gamma + \delta/e$, where $\gamma$ is Euler's constant and $\delta = \int_0^\infty \frac{e^{-t}}{1+t}\,dt$ is the Euler–Gompertz constant, the statement is equivalently the algebraic independence of
--   $$e \quad\text{and}\quad e\gamma + \delta .$$
--
--   This is the case $z=1$ of a classical consequence of Shidlovskii's theorem on algebraic independence of values of $E$-functions (Rivoal 2012, §5, proof of Theorem 2(ii); Shidlovskii, *Transcendental Numbers*, 1989, p. 123), applied to $e^{z}$ and $e^{z}\operatorname{Ein}(z)$.
--
--   **Role.** This is the transcendence input for the mixed Euler–Gompertz programme: it implies at once that $\theta \notin \overline{\mathbb{Q}} + \overline{\mathbb{Q}}\,e$ (theorem `EulerMascheroni.Mixed.expEin_one_not_mem_exp_span`), and in particular that $e\gamma+\delta$ is transcendental.
--
--   **Formalization Note.** `AlgebraicIndependent ℚ ![Complex.exp 1, expEin 1]` is algebraic independence over $\mathbb{Q}$ of the family $(e,\theta)$ indexed by `Fin 2` in $\mathbb{C}$; `expEin 1 = exp 1 * ein 1` with `ein` the power series above (definition `eulerMascheroni_mixedCover`).
-- source:
--   T. Rivoal, On the arithmetic nature of the values of the Gamma function, Euler's constant and Gompertz's constant, Michigan Math. J. 61 (2012), 239-254, https://rivoal.perso.math.cnrs.fr/articles/gammater.pdf : Section 5, proof of Theorem 2(ii) (E(-z) and exp(-z) algebraically independent over Qbar for z in Qbar*, E(z)=sum z^m/(m! m) = -Ein(-z)), and Proposition 1(ii) eq. (2.2) (gamma = Ein(1) - delta/e at z=1). Underlying theorem: Shidlovskii's Second Fundamental Theorem, A. B. Shidlovskii, Transcendental Numbers, de Gruyter Studies in Math. 12, 1989, p. 123 (as cited by Rivoal).

import Definitions.Def_eulerMascheroni_mixedCover
import Mathlib.RingTheory.AlgebraicIndependent.Basic

theorem EulerMascheroni.Mixed.exp_one_expEin_one_algebraicIndependent :
    AlgebraicIndependent ℚ ![Complex.exp 1, EulerMascheroni.Mixed.expEin 1] := by sorry
