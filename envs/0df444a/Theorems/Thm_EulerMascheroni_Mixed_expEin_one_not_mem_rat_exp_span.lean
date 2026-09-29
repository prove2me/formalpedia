-- Prove2me | Theorems.Thm_EulerMascheroni_Mixed_expEin_one_not_mem_rat_exp_span
-- name    : EulerMascheroni.Mixed.expEin_one_not_mem_rat_exp_span
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T17:42:52.867866+00:00
-- url     : https://prove2.me/theorems/7ec2fea7-ae66-4f93-a5e9-7ae9505d21b9
-- title:
--   $e\,\mathrm{Ein}(1)\notin\mathbb Q+\mathbb Q\,e$
-- statement:
--   Let $\operatorname{Ein}(z)=\sum_{n\ge1}\frac{(-1)^{n-1}z^n}{n\cdot n!}$ be the entire complementary exponential integral, and let $A(z)=e^z\operatorname{Ein}(z)$. For all rational numbers $\alpha$ and $\beta$,
--
--   $$
--   A(1)=e\operatorname{Ein}(1)\ne\alpha+\beta e .
--   $$
--
--   That is, $e\operatorname{Ein}(1)$ does not lie in the $\mathbb Q$-span of $1$ and $e$.
--
--   This is the case $c\ne0$ of the $\mathbb Q$-linear independence of $1,e,A(1)$, after dividing a relation $a+be+cA(1)=0$ with rational coefficients by $c$. The complementary case $c=0$ is the irrationality of $e$. It is the rational-coefficient special case of the corresponding statement with real algebraic coefficients.
--
--   **Formalization Note** The comparison is made in $\mathbb C$ using the platform definition `EulerMascheroni.Mixed.expEin`.
-- source:
--   Fischler–Rivoal, Relations between values of arithmetic Gevrey series, and applications to values of the Gamma function, JNT 261 (2024), 36–54, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, Lemma 2(ii), p. 11, and §4.3, p. 15 (integer case a=1, s=1; E_{1,2}(-1)=Ein(1)). This is the coefficient-normalized case c=1 of the linear independence of 1, e, e·Ein(1) stated there (the same source as EulerMascheroni.Mixed.e_values_linear_independent).

import Definitions.Def_eulerMascheroni_mixedCover

theorem EulerMascheroni.Mixed.expEin_one_not_mem_rat_exp_span (α β : ℚ) :
    EulerMascheroni.Mixed.expEin 1 ≠ (α : ℂ) + (β : ℂ) * Complex.exp 1 := by sorry
