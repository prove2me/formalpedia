-- Prove2me | Theorems.Thm_BlackwellDiscreteDP_Stationary_composition_rule
-- name    : BlackwellDiscreteDP.Stationary.composition_rule
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:01:11.777446+00:00
-- url     : https://prove2.me/theorems/dc7e5571-9e5b-40e1-a203-acc0836686ad
-- title:
--   §2 — V(f, π) = L(f)V(π) and V(f₁, ⋯, f_N, π) = L(f₁)⋯L(f_N)V(π)
-- statement:
--   Fix a discount factor $0\le\beta<1$ and recall $L(f)w=r(f)+\beta Q(f)w$. For every decision rule $f$ and policy $\pi$,
--
--   $$V_\beta(f,\pi)=L(f)\,V_\beta(\pi),$$
--
--   and more generally, for decision rules $f_1,\dots,f_N$,
--
--   $$V_\beta(f_1,\dots,f_N,\pi)=L(f_1)\cdots L(f_N)\,V_\beta(\pi).$$
--
--   This is the recursion that underlies Theorems 1 and 2: putting a decision rule in front of a policy acts on returns by the affine monotone map $L(f)$.
--
--   **Formalization Note.** $L(f_1)\cdots L(f_N)V_\beta(\pi)$ is the right fold of the list $[f_1,\dots,f_N]$; for the empty list both sides equal $V_\beta(\pi)$.
-- source:
--   Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962), DOI 10.1214/aoms/1177704593, p. 720, §2 (unnumbered display text)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_Stationary_Model

namespace BlackwellDiscreteDP.Stationary

/-- §2, p. 720 (unnumbered; Blackwell, *Discrete Dynamic Programming*, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593): the composition rule
`V(f, π) = L(f)V(π)` and `V(f₁, ⋯, f_N, π) = L(f₁) ⋯ L(f_N)V(π)`, for `0 ≤ β < 1`.

**Formalization Note.** `L(f₁) ⋯ L(f_N)` applied to `V(π)` is the right fold of the list
`[f₁, …, f_N]`, i.e. `L(f₁)(L(f₂)(⋯ L(f_N)(V(π))))`; the empty list gives `V(π)` itself. -/
theorem composition_rule {St Act : Type} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]
    (M : Model St Act)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (∀ (f : St → Act) (π : Policy St Act),
        M.V β (Policy.cons f π) = M.L β f (M.V β π)) ∧
    (∀ (fs : List (St → Act)) (π : Policy St Act),
        M.V β (Policy.prepend fs π) = fs.foldr (fun f w => M.L β f w) (M.V β π)) := by sorry

end BlackwellDiscreteDP.Stationary
