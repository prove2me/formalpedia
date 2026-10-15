-- Prove2me | Theorems.Thm_AdDataSharing_Topics_proposition_5
-- name    : AdDataSharing.Topics.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:53.237039+00:00
-- url     : https://prove2.me/theorems/38f46768-4377-4612-987b-6804ddcfe4ea
-- title:
--   Proposition 5 (threshold (6) corrected) — both advertisers bid on ADX1 in the unique equilibrium iff $\tau<\tilde\tau$, and $\tilde\tau>1$
-- statement:
--   In the Topics model two advertisers simultaneously bid either on $ADX_1$ (Topics) or on $ADX_2$ (retargeting); a profile is an equilibrium when it is a pure Nash equilibrium of this $2\times 2$ bidding game with the payoffs of p. 17. Throughout, $\alpha\in(0,\tfrac12)$, $0<w<C<M<2C$, $\varphi\in(0,1)$, $\eta_2>0$, $\tau>1$ and $0\le\sigma<1$ (the standing assumptions of the model). Let
--   $$\tilde\tau=\frac{(1+\eta_2)-\sigma(1-\alpha)}{w(1+\eta_2)}\,C+\frac{\sigma(1-\alpha)}{1+\eta_2}.$$
--
--   Then $\tilde\tau>1$, and the following are equivalent:
--
--   1. both advertisers bidding on $ADX_1$ is the unique equilibrium of the Topics bidding game — it is an equilibrium, and every equilibrium has both advertisers on $ADX_1$;
--   2. $\tau<\tilde\tau$.
--
--   Bidding on $ADX_1$ means cross-targeting the rival's website visitors, which the Topics system cannot exclude (p. 17), so the proposition says that both advertisers cross-target exactly when the Topics system is not too inaccurate. It is the main result of §3 and the basis of Proposition 7 and Corollary 2.
--
--   **Formalization Note** The threshold is **corrected**: the paper's display (6) reads $\frac{(1+\eta_2)-\sigma(1-\alpha)}{w}C+\frac{\sigma(1-\alpha)}{1+\eta_2}$, which omits the factor $1/(1+\eta_2)$ on the first term; with the printed threshold the equivalence is false (e.g. $\alpha=\tfrac14$, $M=3$, $C=2$, $w=1$, $\eta_2=1$, $\sigma=\tfrac12$, $\tau=2$). The corrected $\tilde\tau$ solves the page's own deviation condition $(1+\eta_2)(C-\tau w)\ge\sigma(1-\alpha)(C-w)$ for $\tau$. "In the equilibrium" is read as uniqueness: at $\tau=\tilde\tau$ both-on-$ADX_1$ is still an equilibrium but the asymmetric profiles are too. $C>w$ and $\sigma\ge0$ are standing assumptions added as described in the model definition.
-- source:
--   Johnson, Jungbauer, Preuss, Online Advertising, Data Sharing, and Consumer Control, SSRN 3898798 (Nov. 2, 2022), p. 17, Proposition 5, display (6) (corrected: factor 1/(1+η2) on the first term); proof in Appendix pp. 29–30

import Mathlib
import Definitions.Def_AdDataSharing_Topics_Model

namespace AdDataSharing.Topics

theorem proposition_5 (P : Params) (hP : P.Standing) :
    1 < tauTilde P ∧
      ((IsNE P .adx1 .adx1 ∧ ∀ x y : AdDataSharing.Base.Exchange, IsNE P x y → x = .adx1 ∧ y = .adx1) ↔
        P.τ < tauTilde P) := by sorry

end AdDataSharing.Topics
