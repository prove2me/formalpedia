-- Prove2me | Theorems.Thm_AdDataSharing_Topics_proposition_7_ii
-- name    : AdDataSharing.Topics.proposition_7_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:29.653262+00:00
-- url     : https://prove2.me/theorems/f7a7ce8e-5aa7-43cf-83b0-6164890cf7f1
-- title:
--   Proposition 7 (ii) — the threshold $\tilde\tau$ is larger when ADX2 is less efficient ($\sigma$ smaller)
-- statement:
--   Throughout, $\alpha\in(0,\tfrac12)$, $0<w<C<M<2C$, $\varphi\in(0,1)$, $\eta_2>0$, $\tau>1$ and $0\le\sigma<1$ (the standing assumptions of the model). Let $\tilde\tau(\sigma)$ denote the (corrected) threshold of Proposition 5,
--   $$\tilde\tau(\sigma)=\frac{(1+\eta_2)-\sigma(1-\alpha)}{w(1+\eta_2)}\,C+\frac{\sigma(1-\alpha)}{1+\eta_2},$$
--   with all other parameters fixed. If $0\le\sigma'<\sigma$, then
--   $$\tilde\tau(\sigma)<\tilde\tau(\sigma').$$
--
--   A less efficient rival exchange (smaller reach $\sigma$ of retargeting on $ADX_2$) widens the range of inaccuracies $\tau$ for which both advertisers bid on $ADX_1$.
--
--   **Formalization Note** The paper writes "the threshold $\hat\tau$", a slip for $\tilde\tau$, and its proof differentiates the printed (6). For the corrected threshold the slope in $\sigma$ is $(1-\alpha)(1-C/w)/(1+\eta_2)<0$; the statement is the strict monotonicity, not the derivative.
-- source:
--   Johnson, Jungbauer, Preuss, Online Advertising, Data Sharing, and Consumer Control, SSRN 3898798 (Nov. 2, 2022), p. 19, Proposition 7 (ii) ("ˆτ" read as τ̃; threshold corrected); proof Appendix p. 30

import Mathlib
import Definitions.Def_AdDataSharing_Topics_Model

namespace AdDataSharing.Topics

theorem proposition_7_ii (P : Params) (hP : P.Standing) (σ' : ℝ) (hσ'0 : 0 ≤ σ')
    (hσ' : σ' < P.σ) :
    tauTilde P < tauTilde { P with σ := σ' } := by sorry

end AdDataSharing.Topics
