-- Prove2me | Theorems.Thm_DetDLP_bounded_oriented_contraction_step
-- name    : DetDLP.bounded_oriented_contraction_step
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T16:14:57.546287+00:00
-- url     : https://prove2.me/theorems/a76b96e5-10f3-4e6b-ae23-5e5e357a714a
-- title:
--   A single bounded contraction step on the original scalar or terminal graph
-- statement:
--   Choose one placement of all original edges into dyadic packets and one common vertex labeling, with at most three times the original edge count in padded packet slots. At every eligible sample, the split contraction is exactly a weighted sum of products of 64 child contractions over any algebra of the specified binary precision. Each child has at most one sixteenth of the parent edges, the total number of child edges is exactly twice the parent edge count, the maximum child degree is at most the larger of the parent degree and twice the packet length, and terminal legs are balanced for every coordinate simultaneously. The actual legal mode vectors obey the stated exponential branching bound. The case of zero terminal legs includes scalar contractions.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Sections 5.1–5.3, one recursion step with scalar and terminal resource estimates.

import Definitions.Def_DetDLP_OrientedPacketInstance

set_option autoImplicit false
open Finset Polynomial DetDLP.OrientedPacketInstance

namespace DetDLP

theorem bounded_oriented_contraction_step (G : BipartiteMultigraph) {a b : ℕ} (host : Fin b→Fin G.nV) (τ : ℕ)
    (ht : ∀ x,(univ.filter fun y => host x=host y).card≤τ) (hm : 0<G.nE*G.maxDeg)
    (hc : (a+2)*(64^a)^4*G.maxDeg≤G.nE) (hpad : 2^a*(64^a)^2≤G.nE) :
    ∃ (N : ℕ) (active : Fin N→Finset (Pos a)) (L : Fin G.nE ≃ Address active)
      (tag : Fin N→Fin a→Fin 64×Fin 64) (grp : Fin a→Fin G.nV→Fin 64),
    N*2^a≤3*G.nE ∧ (∀ i g,32*(univ.filter fun x => grp i (host x)=g).card≤b+512*(a+2)*τ) ∧
    ∀ (i : Fin a) (p : ℕ) (hp : 0<p) (t : ZMod (2^(a+1))) (ht : t≠0) (hi : padicValNat 2 t.val=i.val)
      (C u : ℝ) (hC : 0≤C) (hu : 0<u) (prec : (p:ℝ)≤C*G.nE*(2:ℝ)^(a-i.val)/u),
    let J := Mode i (fun q => tag q i) p
    let beta := ∀ h,J h→Fin p
    let wt (b : beta) := ∑ h,∑ j : J h,(j.2.val+1)*(b h j).val
    let legal := univ.filter (fun b : beta => wt b<p)
    (legal.card:ℝ)≤Real.exp (3*Real.sqrt (6*C)*G.nE/Real.sqrt u) ∧
    ∃ U : ZMod (2^(a+1))→(ZMod (2^p))[X], Represents t U ∧
    ∀ (R : Type) [CommRing R] [Algebra (ZMod (2^p)) R]
      (T : Fin 64→Type) (V : (v : Fin G.nV)→T (grp i v)→(Fin (G.deg v)→Bool)→R) (z : R),
    ∃ (H : Fin 64→BipartiteMultigraph)
      (child : beta→(g : Fin 64)→T g→(v : Fin (H g).nV)→(Fin ((H g).deg v)→Bool)→R),
      (∀ g,16*(H g).nE≤G.nE) ∧ (∑ g,(H g).nE)=2*G.nE ∧
      (∀ g,(H g).maxDeg ≤ max G.maxDeg (2*2^a)) ∧
      (∀ g,(H g).nV=Fintype.card {v : Fin G.nV // grp i v=g}+N) ∧
      ∀ τ : ∀ g,T g,
        (∑ x : Fin G.nE→Bool,∑ y : Fin G.nE→Bool,
          DeformedContraction.weight (fun v => V v (τ (grp i v))) x y *
            ∏ e,selector G active L U z x y e) =
          ∑ b ∈ legal,(2:R)^(wt b)*∏ g,BTNContract (H g) (child b g (τ g)) := by sorry
end DetDLP
