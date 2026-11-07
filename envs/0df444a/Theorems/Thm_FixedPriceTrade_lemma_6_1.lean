-- Prove2me | Theorems.Thm_FixedPriceTrade_lemma_6_1
-- name    : FixedPriceTrade.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:43:26.557205+00:00
-- url     : https://prove2.me/theorems/8f2f4be8-e697-47da-8ffb-77f3fe3d68c5
-- title:
--   Lemma 6.1 — reference curves for every endpoint
-- statement:
--   Let $d>0$. There is $\bar C(d)>1/4$, namely the solution of $\chi_{\mathrm{end}}(\bar C(d))=d$, such that for $C>0$ the contact parameter $Y_d(C)$ solving $\chi(C,Y_d(C))=d$ under the side conditions of (19) exists uniquely exactly when $C<\bar C(d)$. The map $C\mapsto x(C)$ is a continuous strictly decreasing bijection of $(0,\bar C(d))$ onto $(0,1/d)$. For each such $C$, the reference curve $P_x$ of (22) satisfies
--   $$
--   P_x(a(r))=\frac{e^{-\mathcal I_C(r)/2}}{d\sqrt{D_C(r)}},\qquad a(r)=\frac C{d^2}e^{-\mathcal I_C(r)}\qquad(0\le r\le Y_d(C)),
--   $$
--   is continuously differentiable on $[0,\infty)$, lies below both obstacles, $P_x(a)\le x+a$ and $P_x(a)\le1/d$, and
--   $$
--   Q_x=P_x^{-2}+\big(a(\log P_x)'\big)'
--   $$
--   has no atoms and is given almost everywhere by (24).
--
--   Covering every endpoint, including $C\le1/4$ and $C\ge1/2$ where the closed forms fail, is what makes the comparison global.
--
--   Differences from the source:
--   - reading: there is C̄(d) > 1/4 such that Y_d exists uniquely on 0 < C < C̄(d) → C̄(d) is the solution of χ_end(C̄(d)) = d, and for C > 0 the solution exists uniquely if and only if C < C̄(d); reason: Theorem C and (G2) use C̄(d) as a fixed function of d; the proof (p.15) constructs it so and shows the branch exists exactly on (0, C̄(d)); this reading is stronger than the bare existential
--   - reading: Q_x has no atoms and is given a.e. by (24) → for 0 ≤ a ≤ b, b(log P_x)′(b) − a(log P_x)′(a) = ∫_a^b (Q_x − P_x^{−2}) with Q_x from (24); reason: the derivative measure of a(log P_x)′ is absolutely continuous with density Q_x − P_x^{−2}; this implies the printed claim
--   - encoding: Y_d(C) the solution of (19) → the clause ChiDomain C (Y_d C) ∧ χ(C, Y_d C) = d on (0, C̄(d)); reason: Y_d is a guarded choice in Lean; the clause says it is the solution
--   - encoding: the reference curve P_x indexed by its endpoint x → refCurve d C indexed by the curvature parameter C, with endpoint x(C); C = 0 is the limiting endpoint x = 1/d, P ≡ 1/d (p.16); reason: Lemma 6.1 makes C ↦ x(C) a bijection of (0, C̄(d)) onto (0, 1/d), and p.16 sets the endpoint x = 1/d at C = 0
--   - encoding: continuously differentiable; below both obstacles in (17) → ContDiffOn ℝ 1 on [0, ∞); P ≤ x + a and P ≤ 1/d for a ≥ 0; reason: the obstacles of (17) are x + a and 1/d
--   - encoding: derivatives of absolutely continuous functions (p′, (log p)′, v′) → Mathlib's deriv; reason: deriv agrees almost everywhere with the derivative of an absolutely continuous function, and the derivatives appear only under integrals or a.e. statements
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 26832346…), Lemma 6.1, p.14; proof, pp.15–16

import Mathlib
import Definitions.Def_FixedPriceTrade_refCurve

set_option autoImplicit false

namespace FixedPriceTrade

open MeasureTheory Set

/-- **Lemma 6.1 (reference curves for every endpoint)** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact
Welfare Guarantee of Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…),
p.14.

Let `d > 0`. Then `C̄(d) > 1/4` (with `χ_end(C̄(d)) = d`), and for `C > 0` the contact equation
`χ(C, y) = d` has a unique solution `y` under the side conditions of (19) exactly when
`C < C̄(d)`; `Y_d(C)` is that solution. The map `C ↦ x(C)` is continuous and strictly decreasing
on `(0, C̄(d))` and maps it onto `(0, 1/d)`. For each `C ∈ (0, C̄(d))` the reference curve `P_x`
of (22) satisfies the parametric identity `P_x(a(r)) = e^{−I_C(r)/2}/(d √D_C(r))` for
`0 ≤ r ≤ Y_d(C)`, is continuously differentiable on `[0, ∞)`, lies below both obstacles
`x + a` and `1/d`, and `Q_x = P_x^{−2} + (a (log P_x)′)′` has no atoms and equals (24) almost
everywhere: `a (log P_x)′` is the integral of `Q_x − P_x^{−2}` with `Q_x` from (24).

**Formalization Note.** "There is `C̄(d)`" is read with the `C̄(d)` the proof constructs
(`χ_end(C̄(d)) = d`, p.15), and the branch exists exactly on `(0, C̄(d))` (proof, p.15). "No atoms,
given a.e. by (24)" is encoded as: for `0 ≤ a ≤ b`,
`b (log P)′(b) − a (log P)′(a) = ∫_a^b (Q_x − P_x^{−2})`. -/
theorem lemma_6_1 (d : ℝ) (hd : 0 < d) :
    1 / 4 < Cbar d ∧ chiEnd (Cbar d) = d ∧
    (∀ C, 0 < C → ((∃! y, ChiDomain C y ∧ chi C y = d) ↔ C < Cbar d)) ∧
    (∀ C ∈ Ioo 0 (Cbar d), ChiDomain C (Yd d C) ∧ chi C (Yd d C) = d) ∧
    ContinuousOn (endpointX d) (Ioo 0 (Cbar d)) ∧
    StrictAntiOn (endpointX d) (Ioo 0 (Cbar d)) ∧
    endpointX d '' Ioo 0 (Cbar d) = Ioo 0 (1 / d) ∧
    ∀ C ∈ Ioo 0 (Cbar d),
      (∀ r ∈ Icc 0 (Yd d C), refCurve d C (arcA d C r) = arcP d C r) ∧
      ContDiffOn ℝ 1 (refCurve d C) (Ici 0) ∧
      (∀ a, 0 ≤ a → refCurve d C a ≤ endpointX d C + a ∧ refCurve d C a ≤ 1 / d) ∧
      (∀ a b, 0 ≤ a → a ≤ b →
        b * deriv (fun u => Real.log (refCurve d C u)) b -
            a * deriv (fun u => Real.log (refCurve d C u)) a =
          ∫ u in a..b, (refQ d C u - 1 / refCurve d C u ^ 2)) := by sorry

end FixedPriceTrade
