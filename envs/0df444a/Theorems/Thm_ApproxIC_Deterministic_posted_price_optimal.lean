-- Prove2me | Theorems.Thm_ApproxIC_Deterministic_posted_price_optimal
-- name    : ApproxIC.Deterministic.posted_price_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:38.13821+00:00
-- url     : https://prove2.me/theorems/dba6c235-b185-4acc-92a2-915e0e20ff74
-- title:
--   §2.1, p. 13 — a posted price at a maximizer p⋆ of R is optimal for (P_0), so Π⋆(M(0)) = R(p⋆) = p⋆·F̄(p⋆)
-- statement:
--   Let the buyer's value have a density $f$ on $S=[0,\bar v]$ (standing assumptions of §2), let $R(v)=v\,\bar F(v)$ be the revenue of a posted price $v$, and let $p\in S$ maximize $R$ over $S$. Then the posted-price mechanism at $p$ — allocate and charge $p$ when the report is at least $p$, otherwise allocate nothing and charge nothing — is incentive compatible and individually rational, its revenue is $R(p)$, and no mechanism in $\mathcal M(0)$ earns more:
--   $$\text{posted price }p\in\mathcal M(0),\qquad \Pi(\text{posted price }p)=R(p),\qquad \Pi(m)\le R(p)\ \ \forall m\in\mathcal M(0),$$
--   and consequently
--   $$\Pi^\star(\mathcal M(0)) = R(p) = p\cdot\bar F(p).$$
--
--   This is the classical optimality of posted prices for selling one item to one buyer (Myerson 1981; Riley and Zeckhauser 1983), which the paper recalls on p. 13 and uses in the proof of Theorem 2 as $\Pi^\star(\mathcal M(0))=p^\star\cdot\bar F(p^\star)$. A related platform item is Börgers' Proposition 2.5 (`MechanismDesign.Screening.posted_price_optimal`), which assumes a density that is strictly positive on the support; here the density may vanish on parts of $[0,\bar v]$.
--
--   **Formalization Note** Only the standing density assumptions are used, not bounded variation. Mechanisms are measurable (a disclosed convention of the setting). $\Pi^\star(\mathcal M(0))$ is the `sSup` of the revenue image.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 13, §2.1 (posted-price optimality for (P_0)); used in Appendix B, proof of Theorem 2, p. 53

import Mathlib
import Definitions.Def_ApproxIC_Deterministic_Setting
import Definitions.Def_ApproxIC_Deterministic_HardSoft

namespace ApproxIC.Deterministic

theorem posted_price_optimal (M : Model) (hM : M.Standing) (p : ℝ)
    (hp : p ∈ Set.Icc 0 M.vbar) (hmax : IsMaxOn (R M) (Set.Icc 0 M.vbar) p) :
    postedPrice p ∈ Mset M 0 ∧ revenue M (postedPrice p) = R M p ∧
      IsGreatest (revenue M '' Mset M 0) (R M p) ∧ optRev M 0 = R M p := by sorry

end ApproxIC.Deterministic
