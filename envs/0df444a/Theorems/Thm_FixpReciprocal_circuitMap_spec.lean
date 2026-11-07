-- Prove2me | Theorems.Thm_FixpReciprocal_circuitMap_spec
-- name    : FixpReciprocal.circuitMap_spec
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:53:22.046194+00:00
-- url     : https://prove2.me/theorems/0a99a91a-33f8-433c-8fd9-d467a3164073
-- title:
--   Theorem 4.2 (proof, membership) — $F_{\mathcal C}$ is a continuous self-map given by a polynomial-size circuit, with fixed points $\mathrm{Sol}(\mathcal C)$
-- statement:
--   Let $\tau>0$ be rational and $\mathcal C$ a generalized circuit with the gates of (1) on $N$ variables. Then:
--
--   1. $F_{\mathcal C}$ is continuous on $[0,1]^N$ and maps it to itself;
--   2. $x\in\mathrm{Sol}(\mathcal C)$ if and only if $x\in[0,1]^N$ and $F_{\mathcal C}(x)=x$;
--   3. the explicit data $([0,1]^N,F_{\mathcal C})$ is a basic FIXP instance, its polytope is the cube, its circuit agrees with $F_{\mathcal C}$ on the cube, and the circuit has at most $11N$ operations.
--
--   Clauses 1 and 3 are what make the membership half of the main theorem work.
--
--   Differences from the source:
--
--   - reading: represented by a polynomial-size algebraic circuit → the explicit compiled circuit is a valid basic instance, agrees with F_C on the cube, and has at most 11N operations; reason: the paper's clause states the size bound without a constant; the constants of the compiled circuit are the gates' coefficients, τ, 0 and 1
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), proof of Theorem 4.2, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_FixpReciprocal_basicFIXP
import Definitions.Def_FixpReciprocal_RGate
import Definitions.Def_FixpReciprocal_circuitMap
import Definitions.Def_FixpReciprocal_toBasicData

namespace FixpReciprocal

/-- **Proof of Theorem 4.2, the map `F_C`.** "Each `f_i` is a clipped affine function or `R_τ`, and every reciprocal
denominator satisfies `1 + τ x_j ≥ 1`. Thus `F_C` is a continuous self-map represented by a polynomial-size
algebraic circuit. By definition, `x ∈ Sol(C) ⟺ F_C(x) = x`."

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), proof of Theorem 4.2, p.12.

**Formalization Note.** "Represented by a polynomial-size algebraic circuit" is: `toBasicData τ C` is a basic
instance on the cube, its circuit agrees with `F_C` on the cube, and it has at most `11 N` operations whose
constants are the gate's coefficients, `τ`, `0` and `1`. -/
theorem circuitMap_spec (τ : ℚ) (hτ : 0 < τ) (C : List RGate) (hC : RValid C) :
    ContinuousOn (circuitMap τ C) (cube C.length) ∧
    Set.MapsTo (circuitMap τ C) (cube C.length) (cube C.length) ∧
    (∀ x, x ∈ RCircuitSol τ C ↔ x ∈ cube C.length ∧ circuitMap τ C x = x) ∧
    (toBasicData τ C).IsInstance ∧
    (toBasicData τ C).dom = cube C.length ∧
    (∀ x ∈ cube C.length, (toBasicData τ C).circ.evalOut x = circuitMap τ C x) ∧
    (toBasicData τ C).circ.ops.length ≤ 11 * C.length := by sorry

end FixpReciprocal
