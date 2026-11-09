-- Prove2me | Theorems.Thm_BarelyTestable_LowerBound_repair_propagation
-- name    : BarelyTestable.LowerBound.repair_propagation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:23:22.644179+00:00
-- url     : https://prove2.me/theorems/aa429ae6-9311-4314-a214-bd6c0df8b90b
-- title:
--   Lemma 3.6 — propagation of changes in either half
-- statement:
--   Fix a positive integer $m$, arbitrary labels and table, and an arbitrary real submodular repair $G$. Fix a balanced set $X$ in half $A$, any $Y$ in half $B$, and a slice $\tau\in\{00,01\}$. Let $g(Z)=G(Z,Y,\tau)-F^{(-1)}(Z,Y,\tau)$. If $g(X)\ne0$, then
--
--   $$\#\{(\Gamma,\Gamma')\in\mathcal G_A^2:\ g(X\cup\Gamma)\ne0\ \text{or}\ g(X\setminus\Gamma)\ne0\ \text{or}\ g((X\mathbin\triangle\Gamma)\cup\Gamma')\ne0\}\ge m^{2m}/4.$$
--
--   The corresponding assertion for half $B$, with $X$ fixed and $\tau\in\{10,11\}$, is included. The residual is computed from the actual repair and hard function. Its global submodularity is not an added assumption.
--
--   Differences from the source:
--   - encoding: two action bits and two halves with m blocks of m coordinates → Coord m = Bool ⊕ ((Fin m × Fin m) ⊕ (Fin m × Fin m)); reason: this coordinate type has 2m²+2 elements and coordEquiv explicitly renames it to Fin (2m²+2)
--   - generalization: Lemma 3.6 for the A half (τ ∈ {00,01}, Y fixed), under the standing assumption of §3 (p.11) that m is a large enough integer → both halves selected by a Boolean (side = false is the B half, τ ∈ {10,11}, X fixed), for every m ≥ 1; reason: side = true is exactly the printed lemma; p.14 says the same reasoning applies using 𝒢_B and the soundness proof (p.14) applies the lemma in either half; the p.20 proof uses only balance, which already forces m ≥ 4
--   - encoding: sets Γ selecting exactly one coordinate in each block → functions Fin m → Fin m and their selected sets; reason: this is a bijection, so ordered-pair multiplicity is unchanged
-- source:
--   Diptaksho Palit, Yuichi Yoshida, STOC 2027 submission #722 (October 2026), Lemma 3.6, p. 14 (printed = PDF page); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/722.pdf; PDF SHA256 a095e6ef801edf5b0ce3967efca977e04b7a0b4374e874116509d73837bd14f3

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Loads

set_option autoImplicit false

namespace BarelyTestable.LowerBound

open NonmonotoneSubmod.Shared MeasureTheory

/-- Lemma 3.6, p.14, including its A/B symmetric use in the proof. -/
theorem repair_propagation {m : ℕ} (hm : 1 ≤ m) (r : Sample m)
    (G : Oracle (Coord m)) (hG : Submodular G) (side : Bool) (fixed X : HalfSet m)
    (τ : Bool) (hbal : Balanced X) (hne : residual r G side fixed τ X ≠ 0) :
    (m : ℝ) ^ (2 * m) / 4 ≤ propagatedPairs (residual r G side fixed τ) X := by sorry

end BarelyTestable.LowerBound
