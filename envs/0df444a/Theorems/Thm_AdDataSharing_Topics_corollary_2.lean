-- Prove2me | Theorems.Thm_AdDataSharing_Topics_corollary_2
-- name    : AdDataSharing.Topics.corollary_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:45.412449+00:00
-- url     : https://prove2.me/theorems/42289413-30a9-4575-9e4f-b5e4c411965d
-- title:
--   Corollary 2 — for $\tau$ large enough, ADX1's revenue in every Topics equilibrium is below its revenue in every equilibrium of the base game without Topics
-- statement:
--   In the Topics model two advertisers simultaneously bid either on $ADX_1$ (Topics) or on $ADX_2$ (retargeting); a profile is an equilibrium when it is a pure Nash equilibrium of this $2\times 2$ bidding game with the payoffs of p. 17. Throughout, $\alpha\in(0,\tfrac12)$, $0<w<C<M<2C$, $\varphi\in(0,1)$, $\eta_2>0$, $\tau>1$ and $0\le\sigma<1$ (the standing assumptions of the model).
--
--   Without Topics, ADX1 and the advertisers play the base game of §1 (pp. 4–9): ADX1 first decides whether to allow cross-targeting, then the advertisers decide which exchange to share data with, and an equilibrium is a subgame-perfect equilibrium refined by Assumption 1, with ADX1 earning $\varphi w$ per ad placed on it. That game has the same $\alpha, M, C, w, \varphi, \eta_2$ and, in addition, the look-alike mass $\eta_1\in(0,\eta_2)$ reached when only one advertiser shares data with ADX1.
--
--   Fix all parameters other than $\tau$. Then there is $\bar\tau$ such that for every $\tau>\bar\tau$ the Topics bidding game with inaccuracy $\tau$ has an equilibrium, and for every equilibrium $(x,y)$ of it, every $\eta_1\in(0,\eta_2)$ and every equilibrium $o$ of the base game,
--   $$R^{\mathrm{Topics}}_\tau(x,y) < R^{\mathrm{base}}(o).$$
--   So a regulatory floor $\tau>\bar\tau$ that is too high makes ADX1 better off not introducing Topics.
--
--   **Formalization Note** The base game is the shared definition `AdDataSharing.Base.Model` (mission 1 of this series); its equilibria are `Base.IsEquilibrium` and ADX1's revenue on the equilibrium path is `Base.revenue … o.isOpen o.path`. The statement quantifies over all base equilibria; their existence is Proposition 1 (mission 1), which this statement does not restate. The proof's threshold is $\bar\tau=\frac{[(1+\eta_2)-\sigma]M+\alpha\sigma C}{w(1+\eta_2)}+\frac{\sigma(1-\alpha)}{1+\eta_2}$ (p. 30); the statement asserts existence only. The existence clause for Topics equilibria rules out a vacuous "every equilibrium".
-- source:
--   Johnson, Jungbauer, Preuss, Online Advertising, Data Sharing, and Consumer Control, SSRN 3898798 (Nov. 2, 2022), p. 19, Corollary 2; proof Appendix pp. 30–31

import Mathlib
import Definitions.Def_AdDataSharing_Topics_Model

namespace AdDataSharing.Topics

theorem corollary_2 (P : Params) (hP : P.Standing) :
    ∃ τbar : ℝ, ∀ τ : ℝ, τbar < τ →
      (∃ x y : AdDataSharing.Base.Exchange, IsNE { P with τ := τ } x y) ∧
        ∀ x y : AdDataSharing.Base.Exchange, IsNE { P with τ := τ } x y →
          ∀ (η₁ : ℝ), 0 < η₁ → η₁ < P.η₂ →
            ∀ o : AdDataSharing.Base.Outcome,
              AdDataSharing.Base.IsEquilibrium
                { α := P.α, M := P.M, C := P.C, w := P.w, φ := P.φ, η₁ := η₁, η₂ := P.η₂ } o →
              revenue { P with τ := τ } x y <
                AdDataSharing.Base.revenue
                  { α := P.α, M := P.M, C := P.C, w := P.w, φ := P.φ, η₁ := η₁, η₂ := P.η₂ }
                  o.isOpen o.path := by sorry

end AdDataSharing.Topics
