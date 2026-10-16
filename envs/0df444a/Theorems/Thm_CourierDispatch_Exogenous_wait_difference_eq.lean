-- Prove2me | Theorems.Thm_CourierDispatch_Exogenous_wait_difference_eq
-- name    : CourierDispatch.Exogenous.wait_difference_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T23:12:40.775197+00:00
-- url     : https://prove2.me/theorems/a081ff6e-7e5e-41f3-bdf9-9a923f538331
-- title:
--   (A.1)–(A.2), Online Appendix p. 1 — f(λr) = W_D(λ, μ_D, C_D) − W_B(λ, μ_B, C_B)
-- statement:
--   Let $r>0$, $\lambda>0$ with $\lambda r<\tfrac34$, and let $C_B$ be any real number. With $T_1=\tfrac34$, $T_2=\frac{45\pi}{2(32+15\pi)}$, $C_1=C_D=\tfrac98$ and $C_2=C_B$, put
--   $$f_A(a)=\frac{a^2C_1}{2T_1(T_1-a)}-\frac12-\frac{a^2C_2}{T_2(T_2-a)}-\frac a3 .$$
--   Then
--   $$W_D(\lambda,\mu_D,C_D)-W_B(\lambda,\mu_B,C_B)=\frac{f_A(\lambda r)}{\lambda}.$$
--
--   The difference of the two expected waits depends on $(\lambda,r)$ only through the product $a=\lambda r$, up to the positive factor $1/\lambda$. This reduces both threshold results to a sign analysis of one rational function of one variable.
--
--   **Formalization Note** `lam` is $\lambda$. The paper's $f(a)$ in (A.1) is $f_A(a)/\lambda$, and its $C_2=0.583$ is here the parameter $C_B$; the identity holds for every real $C_B$. The hypothesis $\lambda r<3/4$ keeps both waits inside their stability ranges.
-- source:
--   Chen, Hu, Courier Dispatch in On-Demand Delivery, SSRN 3675063 (version of 2022-09-21), Online Appendix p. 1, proof of Propositions 1 and 2, (A.1)–(A.2)

import Mathlib
import Definitions.Def_CourierDispatch_Exogenous_Setting

namespace CourierDispatch.Exogenous

/-- (A.1)–(A.2), Online Appendix p. 1: `f(λr) = W_D(λ, μ_D, C_D) − W_B(λ, μ_B, C_B)`, where
`f(a) = (1/λ) · fA C_B a`. -/
theorem wait_difference_eq (CB r lam : ℝ) (hr : 0 < r) (hlam : 0 < lam) (hstab : lam * r < TD) :
    WD lam (muD r) CD - WB r lam (muB r) CB = fA CB (lam * r) / lam := by sorry

end CourierDispatch.Exogenous
