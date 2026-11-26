-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_augmented_laplacian_berkowitz_coefficients
-- name    : DirectedHamiltonicity.Main.augmented_laplacian_berkowitz_coefficients
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T15:44:23.590823+00:00
-- url     : https://prove2.me/theorems/147b0237-3ddd-51e6-a6dd-8726f62cca44
-- title:
--   Compute the coefficients of the augmented F₂[y] Laplacian determinant by integer Berkowitz
-- statement:
--   For the augmented reduced Laplacian in Koana and Kumabe, a single charged arithmetic procedure produces the parity of every determinant coefficient in one run. The input supplies any enumeration of the remaining vertices and every surviving or added labelled arc exactly once. It computes a zero-or-one coefficient by a parity scan of the complete arc list, builds a dense matrix of integer polynomials, and calls the actual Berkowitz implementation from STOC #814. Entry degree is bounded by W. The formal cost includes array construction and a per-arc scan charge, followed by the original bit-charge bound for integer polynomial arithmetic.
-- source:
--   Koana and Kumabe, Breaking the 2^n Barrier for Directed Hamiltonicity, Section 4, STOC submission #811, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/811.pdf ; counting Hamiltonian cycles in bipartite digraphs, Section 4, STOC submission #814, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib
import Definitions.Def_DirectedHamiltonicity_Main_DetSum
import Definitions.Def_BipHamCount_Deterministic_Arithmetic
import Theorems.Thm_BipHamCount_Deterministic_berkowitz_det_correct
import Theorems.Thm_BipHamCount_Deterministic_berkowitz_bit_bounds

open scoped Polynomial BigOperators
open DirectedHamiltonicity.Main DirectedHamiltonicity.Main.Multidigraph
open BipHamCount.Deterministic CapacitatedAssort.General

theorem DirectedHamiltonicity.Main.augmented_laplacian_berkowitz_coefficients :
    ∃ solve : {V E : Type} → [DecidableEq V] → {n : ℕ} → ℕ → (E → V) → (E → V) →
        (E → ℕ) → (Fin n → V) → List E → Work ZPoly,
      ∀ {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        (H : Multidigraph V E) (w : E → ℕ) (s t : V) (S : Finset (Internal s t))
        (R : (i : Internal s t) → Finset (H.incomingWeights w i.1)) (W : ℕ),
        (∀ e, w e ≤ W) → ∀ (n : ℕ) (order : Fin n ≃ {v // v ≠ s})
        (L : List ({e // H.KeepArc s t S e} ⊕ H.AugArc w s t R)),
        (∀ e, e ∈ L) → L.Nodup → ∀ start : ℕ,
        let D := W+1
        let G := H.subXR w s t S R
        let labels : ({e // H.KeepArc s t S e} ⊕ H.AugArc w s t R) → ℕ :=
          Sum.elim (fun e => w e.1) (fun a => a.2.1.1)
        let z := (solve D G.tail G.head labels (fun i => (order i).val) L).run start
        let prep := 1+n*(1+(1+n*(1+(1+D*(1+L.length)))))
        let Tbits := D+(n+1)*(2*D+n+4)
        let p := fun l : ℕ => 1+l*(2*Tbits+n+4)
        let g := p (n+1)+Tbits+D+n+5
        let b := 100*(g+2)^4+8*(n+3)+16
        let h := 16*(n+3)
        let T := (n+1)*(10*(h*(h*(h*b))))+b+b
        (∀ k : ℕ, ((((z.1[k]?).getD 0 : ℤ) : ZMod 2)) =
          (H.augLaplacian w s t S R).det.coeff k) ∧ z.2 ≤ start + prep + T := by sorry
