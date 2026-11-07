-- Prove2me | Theorems.Thm_EffHorizonProphet_f_le_at_xStar
-- name    : EffHorizonProphet.f_le_at_xStar
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:45:17.371187+00:00
-- url     : https://prove2.me/theorems/86b98efc-9845-4b88-9f33-36bb1c6e162a
-- title:
--   Eq. (20)–(24) — the global maximizer and the closed form
-- statement:
--   Fix $S\ge1$ and $\tilde\gamma\in[0,1]$. Then:
--
--   1. $y_{\tilde\gamma}\ge0$;
--   2. $x\mapsto f_S(x,y_{\tilde\gamma})$ attains its global maximum over $x>0$ at $x_{\tilde\gamma}$;
--   3. $f_S(x_{\tilde\gamma},y_{\tilde\gamma})=A_S(x_{\tilde\gamma})$;
--   4. $A_S(x_{\tilde\gamma})=U(S,\tilde\gamma)$.
--
--   This solves the minimax problem $\inf_{y\ge0}\sup_{x>0}f_S(x,y)$ from above and identifies the constant of Theorem 1.
--
--   Differences from the source:
--   - encoding: $\sup_{x>0}f_S(x,y_{\tilde\gamma})=f_S(x_{\tilde\gamma},y_{\tilde\gamma})$ → $f_S(x,y_{\tilde\gamma})\le f_S(x_{\tilde\gamma},y_{\tilde\gamma})$ for all $x>0$; reason: this is what it means for $x_{\tilde\gamma}>0$ to attain the supremum
--   - encoding: phases and stages are numbered from $1$ → they are numbered from $0$; reason: a relabelling: paper phase $s$ is Lean phase $s-1$
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Eq. (20)–(24), pp.22–23; closed form, p.6

import Mathlib
import Definitions.Def_EffHorizonProphet_fS
import Definitions.Def_EffHorizonProphet_xStar
import Definitions.Def_EffHorizonProphet_yStar
import Definitions.Def_EffHorizonProphet_optRatio

namespace EffHorizonProphet

/-- **Eq. (20)–(24) and the closed form** (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), pp.22–23; closed form p.6): `y_γ̃ ≥ 0`;
`x ↦ f_S(x, y_γ̃)` attains its global maximum at `x_γ̃`; the maximum is `A_S(x_γ̃)`; and `A_S(x_γ̃)`
equals the right-hand side of Theorem 1. -/
theorem f_le_at_xStar (S : ℕ) (hS : 1 ≤ S) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    0 ≤ yStar S γ ∧
      (∀ x, 0 < x → fS S γ x (yStar S γ) ≤ fS S γ (xStar S γ) (yStar S γ)) ∧
      fS S γ (xStar S γ) (yStar S γ) = AS S γ (xStar S γ) ∧
      AS S γ (xStar S γ) = optRatio S γ := by sorry

end EffHorizonProphet
