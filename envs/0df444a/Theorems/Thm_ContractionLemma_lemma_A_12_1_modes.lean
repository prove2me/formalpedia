-- Prove2me | Theorems.Thm_ContractionLemma_lemma_A_12_1_modes
-- name    : ContractionLemma.lemma_A_12_1_modes
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:04:36.759321+00:00
-- url     : https://prove2.me/theorems/c4f2ff70-986e-4f14-ba31-da2a111ff0c8
-- title:
--   Lemma A.12.1 — modes: what a row bit hears splits modulo $2^{p^\prime}$
-- statement:
--   Fix $t\in\mathcal E\setminus\{-L\}$ of level $i$, a precision $p'$ and a node $z_j\in\mathcal O$, and put $T=t+\alpha z_j$. The modes $\xi$ are moments of the column bits of one tile, with weights $w_\xi\ge 1$, and:
--
--   1. there are at most $6M/D_i$ modes of each weight, where $D_i=L/2^i$;
--   2. for a row bit $x$ in a level-$i$ group $g$,
--   $$
--   (W(T)X)_x\equiv\omega_x+\sum_\xi c_{x,\xi}\,\xi\pmod{2^{p'}},
--   $$
--   where $\omega_x$ involves only column bits of $g$ in $x$'s packet, the sum involves only modes of $x$'s packet sent to $g$ by another group, and each coefficient $c_{x,\xi}$ is a constant, not depending on the bits, and divisible by $2^{w_\xi}$.
--
--   Modes are shared by all rows that hear a tile, which is what compresses the crossings.
--
--   **Formalization Note** Modes, $\omega_x$ and $c_{x,\xi}$ are the defined objects of the proof. The labels and packets are those of Lemma A.9, through orientation and at most $3M/L$ packets.
--
--   Differences from the source:
--   - reading: there are modes ξ → the defined modes of the proof, for tiles that some row bit crosses into; reason: Lemma A.12.2 and A.18 use these same objects; every other tile of the proof has coefficient 0
--   - reading: a node z_j ∈ O → a binary node ∑ b_k U^k; reason: these are the nodes defined on p.96
--   - reading: the setting of Lemma A.12.1 (labels and packets of Lemma A.9) → orientation and at most 3M/L packets as hypotheses; reason: these are the facts of Lemma A.9 the proof uses
--   - reading: the second part involves only modes of x's packet sent to g by another group → every mode with c_{x,ξ} ≠ 0 is in x's packet and is sent by a group other than that of x; reason: a mode is involved in the sum exactly when its coefficient is nonzero
--   - generalization: O = Z_(2)[U]/(f) with f of degree 4λ → every monic f with f mod 2 irreducible, of any degree; reason: the paper picks one such f by search; degree 4λ is a special case
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Lemma A.12.1, p.67; proof pp.88–89

import Mathlib
import Definitions.Def_ContractionLemma_BipNet
import Definitions.Def_ContractionLemma_BipNet_Phi
import Definitions.Def_ContractionLemma_kernel
import Definitions.Def_ContractionLemma_Placement
import Definitions.Def_ContractionLemma_Packing
import Definitions.Def_ContractionLemma_zoom
import Definitions.Def_ContractionLemma_Et
import Definitions.Def_ContractionLemma_NodeField
import Definitions.Def_ContractionLemma_Splitting_modeSet
import Definitions.Def_ContractionLemma_Splitting_childNet

set_option autoImplicit false

namespace ContractionLemma

open Polynomial

/-- **Lemma A.12.1 (Modes)** — Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript,
sha256 049caea1…), p.67 (PDF p.70); proof pp.88–89.

Fix `t ∈ E \ {−L}` of level `i`, a precision `p′` and a node `z_j`, put `T = t + αz_j`, and take
labels and packets as in Lemma A.9. The modes `ξ` are moments of the column bits of one tile, with
weight `w_ξ ≥ 1`, and:
(a) there are at most `6M/D_i` modes of each weight, `D_i = L/2^i`;
(b) for a row bit `x` of the level-`i` group `g`,
`(W(T)X)_x ≡ ω_x + ∑_ξ c_{x,ξ} ξ (mod 2^{p′})`, where `ω_x` involves only column bits of `g` in `x`'s
packet, the sum involves only modes of `x`'s packet sent to `g` by another group, and each
coefficient `c_{x,ξ}` is a constant divisible by `2^{w_ξ}`.

**Formalization Note.** Modes, `ω_x` and `c_{x,ξ}` are the constructions of the proof
(`Splitting.modeSet`, `Splitting.omega`, `Splitting.coef`). A mode "involved" in the sum of `x` is
one with `c_{x,ξ} ≠ 0`. A coefficient depends on no bit by its type. The left side is the sum over
`e'` of `W_{e,e'}(T) X_{e'}`. The tiles kept in `modeSet` are those a row bit crosses into (see its
note); the other tiles of the proof carry coefficient `0` for every row bit. -/
theorem lemma_A_12_1_modes {U W E : Type*} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
    [Fintype E] [DecidableEq E] (f : ℤ[X]) (dg : ℕ) (hf : IsNodePoly f dg) (a : ℕ)
    (G : BipNet U W E (NodeField f)) (pk : Packing U W E a)
    (hor : pk.Orientation G.rowOf G.colOf) (hfew : pk.FewPackets)
    (t : ℤ) (ht : t ∈ easyPts a) (htL : t ≠ -(2 ^ a : ℤ)) (i : ℕ) (hi : i = padicValInt 2 t)
    (p' : ℕ) (b : Fin f.natDegree → Bool) :
    (∀ ξ : Splitting.Mode G pk i p', 1 ≤ Splitting.weight ξ) ∧
    (∀ w : ℕ, ((Finset.univ.filter fun ξ : Splitting.Mode G pk i p' =>
        Splitting.weight ξ = w).card : ℝ) ≤ 6 * Fintype.card E / 2 ^ (a - i)) ∧
    (∀ (e : E) (X : E → Bool),
      CongrO f p' (∑ e', if X e' then Splitting.wEntry pk t (binNode f b) e e' else 0)
        (Splitting.omega G pk t i (binNode f b) e X +
          ∑ ξ : Splitting.Mode G pk i p',
            Splitting.coef G pk t i (binNode f b) p' e ξ * Splitting.modeVal G pk i p' ξ X)) ∧
    (∀ (e : E) (X X' : E → Bool),
      (∀ e', pk.packet e' = pk.packet e →
        pk.colSym (G.colOf e') i = pk.rowSym (G.rowOf e) i → X e' = X' e') →
      Splitting.omega G pk t i (binNode f b) e X = Splitting.omega G pk t i (binNode f b) e X') ∧
    (∀ (e : E) (ξ : Splitting.Mode G pk i p'),
      Splitting.coef G pk t i (binNode f b) p' e ξ ≠ 0 →
      ξ.1.1 = pk.packet e ∧
      ∃ g', g' ≠ pk.rowSym (G.rowOf e) i ∧ Splitting.SentBy G pk i p' g' ξ) ∧
    (∀ (e : E) (ξ : Splitting.Mode G pk i p'),
      CongrO f (Splitting.weight ξ) (Splitting.coef G pk t i (binNode f b) p' e ξ) 0) := by sorry

end ContractionLemma
