-- Prove2me | Theorems.Thm_AlgoTransparency_eq_12_thresholds
-- name    : AlgoTransparency.eq_12_thresholds
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:52:40.633269+00:00
-- url     : https://prove2.me/theorems/db1cb4b7-9d52-4b9b-9d6f-1bc18b784e7d
-- title:
--   Eq. (12): the firm's indifference thresholds $0<\gamma_{th1}<\gamma_{th0}<1$
-- statement:
--   Assume the standing assumptions and put $\gamma_{th0}=R/\alpha$ and $\gamma_{th1}=(R-\beta)/\alpha$. Then:
--
--   1. $0<\gamma_{th1}<\gamma_{th0}<1$;
--   2. at every occupied opaque state $S$ (that is, $n_S=n^H_S+n^L_S>0$), with $\gamma^E_S=n^H_S/n_S$ the share of H agents in $S$, the firm's margin $m_S=n^H_S(W^H_S-R)+n^L_S(W^L_S-R)$ satisfies
--   $$
--   m_S=0\iff\gamma^E_S=\gamma_{th}(S),\qquad m_S>0\iff\gamma^E_S>\gamma_{th}(S),\qquad m_S<0\iff\gamma^E_S<\gamma_{th}(S),
--   $$
--   where $\gamma_{th}(S)=\gamma_{th0}$ for $S\in\{A,C\}$ and $\gamma_{th}(S)=\gamma_{th1}$ for $S\in\{B,D\}$;
--   3. the same holds in the transparent game, with $\gamma_{th0}$ at $E$ and $\gamma_{th1}$ at $F$.
--
--   The firm hires a state when the share of H agents there exceeds the threshold and rejects it when the share falls below; every equilibrium computation of the paper rests on this.
--
--   Differences from the source:
--   - generalization: (12): the firm is indifferent iff γ^E_S = (R − W^L_S)/(W^H_S − W^L_S) → the indifference and both strict sign equivalences; reason: m_S = n_S α (γ^E_S − γ_th), so the strict cases are the same computation; specializes to (12)
--   - generalization: strategies q_H, q_L ∈ [0,1] → any real q_H, q_L with n_S > 0; reason: the statement is an algebraic identity in the masses; specializes to q ∈ [0,1]
--   - reading: θ and 1 − θ are "portions"; 0 < θ < 1 is never written → Standing includes 0 < θ < 1; reason: the paper divides by θ and 1 − θ
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, §4.1, eq. (12), p.17 (PDF 18); §4.2, pp.19–20 (PDF 20–21)

import Mathlib
import Definitions.Def_AlgoTransparency_Standing
import Definitions.Def_AlgoTransparency_marginO
import Definitions.Def_AlgoTransparency_marginT

namespace AlgoTransparency

/-- **Eq. (12) and the thresholds `γ_th0`, `γ_th1`**, Wang, Huang, Jasin & Singh,
arXiv:2008.09283v1, §4.1, p.17 (PDF 18), and §4.2, pp.19–20 (PDF 20–21).

Under the standing assumptions:

1. `0 < γ_th1 < γ_th0 < 1`, where `γ_th0 = R/α` and `γ_th1 = (R − β)/α`;
2. at every occupied opaque state `S` (`n_S = n^H_S + n^L_S > 0`), with `γ^E_S = n^H_S/n_S`, the
   firm's margin `m_S` is zero, positive or negative exactly when `γ^E_S` equals, exceeds or falls
   below the threshold `γ_th0` (for `S ∈ {A, C}`) or `γ_th1` (for `S ∈ {B, D}`);
3. the same holds in the transparent game, with `γ_th0` at `E` and `γ_th1` at `F`.

**Formalization Note.** The paper states the indifference (`m_S = 0`) form of (12); the sign
form is the same computation, since `m_S = n_S α (γ^E_S − γ_th)`. No bound on the strategies
`qH, qL` is needed, only `n_S > 0`. -/
theorem eq_12_thresholds (p : Params) (hp : Standing p) :
    (0 < (p.R - p.β) / p.α ∧ (p.R - p.β) / p.α < p.R / p.α ∧ p.R / p.α < 1) ∧
    (∀ (qH qL : ℝ) (S : OState), 0 < massHO p qH S + massLO p qL S →
      let γ := massHO p qH S / (massHO p qH S + massLO p qL S)
      let γth : ℝ := match S with
        | .A => p.R / p.α
        | .B => (p.R - p.β) / p.α
        | .C => p.R / p.α
        | .D => (p.R - p.β) / p.α
      (marginO p qH qL S = 0 ↔ γ = γth) ∧ (0 < marginO p qH qL S ↔ γth < γ) ∧
        (marginO p qH qL S < 0 ↔ γ < γth)) ∧
    (∀ (qH qL : ℝ) (S : TState), 0 < massHT p qH S + massLT p qL S →
      let γ := massHT p qH S / (massHT p qH S + massLT p qL S)
      let γth : ℝ := match S with
        | .E => p.R / p.α
        | .F => (p.R - p.β) / p.α
      (marginT p qH qL S = 0 ↔ γ = γth) ∧ (0 < marginT p qH qL S ↔ γth < γ) ∧
        (marginT p qH qL S < 0 ↔ γ < γth)) := by sorry

end AlgoTransparency
