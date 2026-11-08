-- Prove2me | Theorems.Thm_AffDisp4n_affine_reparameterisation
-- name    : AffDisp4n.affine_reparameterisation
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:04:25.460006+00:00
-- url     : https://prove2.me/theorems/3d199fbd-c171-45e1-92b9-29dd6b563c31
-- title:
--   §3.2 (AR) — exchanging a parameter and an auxiliary variable keeps validity, $m$, $q$, $s$ and $W$
-- statement:
--   Let $\sigma$ be a state valid for the original circuit $C_0$. Let $Q$ be an auxiliary variable and $x$ an unpaired parameter such that $Q$ depends on $x$: the coefficient of $x$ in the solved form $Q = (A^{-1} N u + A^{-1} c)_Q$ is $1$, so $Q = x + \varphi(u_{-x})$. Let $\sigma'$ be the result of the exchange (AR), which substitutes $x \leftarrow w + \varphi(u_{-x})$ in $\Phi$, regards $Q$ as the new parameter $w$ and $x$ as an auxiliary variable. Then $\sigma'$ is again valid for $C_0$, and
--   $$
--   \Delta m = \Delta q = \Delta a = \Delta s = 0, \qquad \Delta W = 0 .
--   $$
--
--   (AR) changes the parameters without changing the circuit or $\operatorname{im} \Phi$. The paper uses it to turn both inputs of a minimal AND into parameters (§4.2) and inside deletion (D4).
--
--   **Formalization Note** The exchange is the explicit `State.arExchange`. Validity of the result includes invertibility of the new auxiliary matrix (§2.6) and the invariant $C(u) = C_0(\Phi(u))$ on $Z(P)$.
--
--   Differences from the source:
--   - generalization: the current state of the gate elimination algorithm → any state σ valid for C₀ (State.Valid: Φ injective, disjoint pairs, A invertible, at most three nonconstant terms per equation, C(u) = C₀(Φ(u)) on Z(P)); reason: the paper's argument uses only these invariants and every state of the algorithm is valid (§2.4, p.16), so the statement specializes to the algorithm's states
--   - encoding: substitute x ← w + φ(u₋ₓ) in Φ, regard Q as the new parameter w and x as an auxiliary variable; exchange the column of x in N with the column of Q in A → State.arExchange j x: Φ ∘ τ written as translation b + κ·L₍·x₎ and linear part L·T, columns exchanged, circuit inputs x and Q swapped; reason: the definition writes out the paper's substitution; the new w takes the index of x and x the index of Q
--   - encoding: Q depends on the unpaired parameter x (Q = x + φ(u₋ₓ)) → (A⁻¹ N) j x = 1 and x unpaired; reason: the coefficient of x in the solved form of Q
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §3.2, pp.20–21, paragraph "AR: exchanging a parameter and an auxiliary variable"; §2.6, pp.18–19

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_Acyclic_gateVal
import Definitions.Def_AffDisp4n_Acyclic_eval
import Definitions.Def_AffDisp4n_Circuit
import Definitions.Def_AffDisp4n_Acyclic_mapInput
import Definitions.Def_AffDisp4n_Acyclic_Reads
import Definitions.Def_AffDisp4n_PairsDisjoint
import Definitions.Def_AffDisp4n_Z
import Definitions.Def_AffDisp4n_IsAffineOp
import Definitions.Def_AffDisp4n_IsAndOp
import Definitions.Def_AffDisp4n_State
import Definitions.Def_AffDisp4n_State_Phi
import Definitions.Def_AffDisp4n_State_eval
import Definitions.Def_AffDisp4n_State_Valid
import Definitions.Def_AffDisp4n_State_s
import Definitions.Def_AffDisp4n_State_q
import Definitions.Def_AffDisp4n_State_a
import Definitions.Def_AffDisp4n_State_IsPaired
import Definitions.Def_AffDisp4n_State_deg
import Definitions.Def_AffDisp4n_State_W
import Definitions.Def_AffDisp4n_State_D1Applicable
import Definitions.Def_AffDisp4n_State_D2Applicable
import Definitions.Def_AffDisp4n_State_D3Applicable
import Definitions.Def_AffDisp4n_State_D4Applicable
import Definitions.Def_AffDisp4n_State_AffineMovable
import Definitions.Def_AffDisp4n_State_Reduced
import Definitions.Def_AffDisp4n_State_OutputSimple
import Definitions.Def_AffDisp4n_State_Case1Applicable
import Definitions.Def_AffDisp4n_State_Case2Applicable
import Definitions.Def_AffDisp4n_State_Case3Applicable
import Definitions.Def_AffDisp4n_State_arExchange

namespace AffDisp4n

/-- **(AR): exchanging a parameter and an auxiliary variable** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §3.2, pp.20–21, with §2.6
"Preserving the representation", pp.18–19). Let `Q` (auxiliary variable `j`) depend on the unpaired
parameter `x`, i.e. the coefficient of `x` in the solved form `Q = (A⁻¹ N u + A⁻¹ c)_j` is `1`, so
`Q = x + φ(u₋ₓ)`. Substituting `x ← w + φ(u₋ₓ)` in `Φ`, regarding `Q` as the new parameter `w` and `x` as
an auxiliary variable (`State.arExchange`) gives a state that is again valid for the original circuit
`C₀`, with "∆m = ∆q = ∆a = ∆s = 0" and "∆W = 0".

**Formalization Note** Validity of the new state contains the invertibility of the new auxiliary
matrix (§2.6, p.19), the unchanged three-term bound, injectivity of `Φ ∘ τ`, and the invariant
`C(u) = C₀(Φ(u))` on `Z(P)` (§2.4, p.16). -/
theorem affine_reparameterisation {n : ℕ} (C₀ : Circuit n) (σ : State n) (hσ : σ.Valid C₀)
    (j : Fin σ.r) (x : Fin σ.m) (hx : ¬ σ.IsPaired x) (hQx : (σ.A⁻¹ * σ.N) j x = 1) :
    (σ.arExchange j x).Valid C₀ ∧ (σ.arExchange j x).m = σ.m ∧ (σ.arExchange j x).q = σ.q ∧
      (σ.arExchange j x).s = σ.s ∧ (σ.arExchange j x).W = σ.W := by sorry

end AffDisp4n
