-- Prove2me | Theorems.Thm_DetDLP_active_scalar_packet_recursion_node
-- name    : DetDLP.active_scalar_packet_recursion_node
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T16:34:11.516191+00:00
-- url     : https://prove2.me/theorems/192e22a6-19c5-4f60-ab95-a02a15c7d81d
-- title:
--   The scalar recursion node at the actual degree-sensitive parameters
-- statement:
--   Starting with the scalar theorem’s exact root degree cutoff and logarithmic scale, take the prescribed floored windows, packet widths and accumulated tapered Hermite precisions. Every sufficiently large active call has enough real edges for packing, enough binary lifts for coefficient interpolation, and a nonempty window. At every admissible sample the original contraction factors into weighted products of 64 child contractions. Each child has at most M/16 edges, all children together have 2M edges, and their maximum degree stays below the original cutoff. The cardinality of actual legal mode vectors is at most exp(3 sqrt(246) M/sqrt(u)), and the same labels balance any supplied terminal hosts.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Sections 5.2 and 5.3, applicability of the integer depth schedule and finite-ring branching on active scalar paths.

import Definitions.Def_DetDLP_OrientedPacketInstance

set_option autoImplicit false
open Finset Polynomial DetDLP.OrientedPacketInstance

namespace DetDLP

theorem active_scalar_packet_recursion_node (C : ℕ) (hc : 0<C) :
    ∃ R₀ : ℕ,∀ (root G : BipartiteMultigraph) (β d : ℕ) (pin m past : ℕ→ℕ)
      {b : ℕ} (host : Fin b→Fin G.nV) (τ : ℕ),
    let Δ := max root.maxDeg (Nat.ceil ((β:ℝ)^((9:ℝ)/10)))
    let ρ := max 1 (Nat.floor (Real.logb 2 ((β:ℝ)/(Δ:ℝ))))
    let u (j : ℕ) := ρ/(131072*2^j)
    let a (j : ℕ) := 2*∑ v ∈ range (j+1),u v
    let h (j : ℕ) := (3*m j+u j-1)/u j
    let precision (j z : ℕ) := pin j+8*h j*2^(a j-z)+8*m j*(a j+1)
    2≤β→R₀≤ρ→0<G.nE→m d=G.nE→β≤G.nE*(ρ.sqrt+1)→G.nE*8^d≤C*β→
    G.maxDeg≤Δ→pin 0≤C*β→(∀ j<d,m j≤C*β)→(∀ j<d,pin (j+1)≤precision j (past j))→
    (∀ x,(univ.filter fun y => host x=host y).card≤τ)→
    0<u d ∧ u d≤G.nE ∧ u d≤a d ∧ G.nE*(2^(a d+1)-1)+1≤2^(4*Nat.clog 2 β) ∧
    ∃ (N : ℕ) (active : Fin N→Finset (Pos (a d))) (L : Fin G.nE ≃ Address active)
      (tag : Fin N→Fin (a d)→Fin 64×Fin 64) (grp : Fin (a d)→Fin G.nV→Fin 64),
    N*2^(a d)≤3*G.nE ∧ (∀ i g,32*(univ.filter fun x => grp i (host x)=g).card≤b+512*(a d+2)*τ) ∧
    ∀ (i : Fin (a d)) (hi : i.val<u d) (t : ZMod (2^(a d+1))) (ht : t≠0) (hval : padicValNat 2 t.val=i.val),
    let p := precision d i.val
    let J := Mode i (fun q => tag q i) p
    let beta := ∀ h,J h→Fin p
    let wt (b : beta) := ∑ h,∑ j : J h,(j.2.val+1)*(b h j).val
    let legal := univ.filter (fun b : beta => wt b<p)
    (legal.card:ℝ)≤Real.exp (3*Real.sqrt (246:ℝ)*G.nE/Real.sqrt (u d)) ∧
    ∃ U : ZMod (2^(a d+1))→(ZMod (2^p))[X], Represents t U ∧
    ∀ (R : Type) [CommRing R] [Algebra (ZMod (2^p)) R]
      (T : Fin 64→Type) (V : (v : Fin G.nV)→T (grp i v)→(Fin (G.deg v)→Bool)→R) (z : R),
    ∃ (H : Fin 64→BipartiteMultigraph)
      (child : beta→(g : Fin 64)→T g→(v : Fin (H g).nV)→(Fin ((H g).deg v)→Bool)→R),
      (∀ g,16*(H g).nE≤G.nE) ∧ (∑ g,(H g).nE)=2*G.nE ∧
      (∀ g,(H g).maxDeg≤Δ) ∧
      (∀ g,(H g).nV=Fintype.card {v : Fin G.nV // grp i v=g}+N) ∧
      ∀ τ : ∀ g,T g,
        (∑ x : Fin G.nE→Bool,∑ y : Fin G.nE→Bool,
          DeformedContraction.weight (fun v => V v (τ (grp i v))) x y *
            ∏ e,selector G active L U z x y e) =
          ∑ b ∈ legal,(2:R)^(wt b)*∏ g,BTNContract (H g) (child b g (τ g)) := by sorry
end DetDLP
