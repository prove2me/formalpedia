-- Prove2me | Theorems.Thm_DetDLP_m89_s1_query_graph_words
-- name    : DetDLP.m89_s1_query_graph_words
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T00:37:55.758804+00:00
-- url     : https://prove2.me/theorems/01e98075-9658-43c3-b927-5fab2bbcf4f1
-- title:
--   Compile legal scalar queries to succinct parsimonious graph instances
-- statement:
--   Assuming the modular and elliptic-curve gadget identities, two total polynomial-time word functions suffice for graph-instance preparation and port evaluation. A legal query has a Boolean relation with exactly the requested number of witnesses and a parsimonious graph for that relation. The edge count is less than the precision, the degree obeys the contraction cutoff, and the scale plus the query length is linear in the product of the block count and field bit length. The public descriptor is the original query.
-- source:
--   S. Liu, B. Zhang, and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2 (pp. 11–13), proof of Theorem 3.1; Stage I machine model of Section 2.

import Definitions.Def_ToTuring_PolyT
import Definitions.Def_DetDLP_M89_S1_Queries
set_option autoImplicit false
open DetDLP DetDLP.M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.m89_s1_query_graph_words :
    ((∀ (q x y z : ℕ) (γ : Bool) (ssum : ℕ),
        x < q → y < q → z < q →
        ((x + y = ssum ∧ z + (if γ then 1 else 0) * q = ssum) ↔
          (z = (x + y) % q ∧ γ = decide (q ≤ x + y) ∧ ssum = x + y))) ∧
     (∀ (q x y z θ u₁ u₂ : ℕ),
        x < q → y < q → z < q →
        ((x * y = u₁ ∧ θ * q = u₂ ∧ u₂ + z = u₁) ↔
          (z = (x * y) % q ∧ θ = (x * y) / q ∧ θ < q ∧ u₁ = x * y ∧ u₂ = ((x * y) / q) * q))) ∧
     (∀ (p : ℕ) [Fact p.Prime] (u : ZMod p) (ζ : Bool) (winv : ZMod p),
        (((if ζ then (1 : ZMod p) else 0) * u = 0 ∧
          (if ζ then (1 : ZMod p) else 0) * winv = 0 ∧
          (1 - (if ζ then (1 : ZMod p) else 0)) * (u * winv) =
            1 - (if ζ then (1 : ZMod p) else 0)) ↔
         (ζ = decide (u = 0) ∧ winv = u⁻¹))) ∧
     ((∀ (ι₁ ι₂ ζx ζy : Bool),
         let b : Bool → ℤ := fun x => if x then 1 else 0
         let σ₁ := b ι₁
         let σ₂ := (1 - b ι₁) * b ι₂
         let σ₃ := (1 - b ι₁) * (1 - b ι₂) * b ζx * b ζy
         let σ₄ := (1 - b ι₁) * (1 - b ι₂) * (1 - b ζx)
         let σ₅ := (1 - b ι₁) * (1 - b ι₂) * b ζx * (1 - b ζy)
         (σ₁ = 0 ∨ σ₁ = 1) ∧ (σ₂ = 0 ∨ σ₂ = 1) ∧ (σ₃ = 0 ∨ σ₃ = 1) ∧
         (σ₄ = 0 ∨ σ₄ = 1) ∧ (σ₅ = 0 ∨ σ₅ = 1) ∧
         σ₁ + σ₂ + σ₃ + σ₄ + σ₅ = 1) ∧
      (∀ (p : ℕ) [Fact p.Prime], 2 < p →
         ∀ (aE bE x₁ y₁ x₂ y₂ lsl : ZMod p) (ι₁ ι₂ : Bool),
           y₁ ^ 2 = x₁ ^ 3 + aE * x₁ + bE →
           y₂ ^ 2 = x₂ ^ 3 + aE * x₂ + bE →
           let ζx := decide (x₂ - x₁ = 0)
           let ζy := decide (y₁ + y₂ = 0)
           let b : Bool → ZMod p := fun x => if x then 1 else 0
           let σ₄ := (1 - b ι₁) * (1 - b ι₂) * (1 - b ζx)
           let σ₅ := (1 - b ι₁) * (1 - b ι₂) * b ζx * (1 - b ζy)
           ((σ₄ * ((x₂ - x₁) * lsl - (y₂ - y₁)) = 0 ∧
             σ₅ * (2 * y₁ * lsl - (3 * x₁ ^ 2 + aE)) = 0 ∧
             (1 - σ₄ - σ₅) * lsl = 0) ↔
            lsl =
              if (!ι₁ && !ι₂ && !ζx) then (y₂ - y₁) * (x₂ - x₁)⁻¹
              else if (!ι₁ && !ι₂ && ζx && !ζy) then (3 * x₁ ^ 2 + aE) * (2 * y₁)⁻¹
              else 0)))) →
    ∃ (make port : List Bool → List Bool) (L : ℕ), Groundwork.PolyT make ∧ Groundwork.PolyT port ∧
      ∀ w b n, Query w b n → ∃ (s : ℕ) (G : BipartiteMultigraph)
        (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
        (k : ℕ) (ext : Fin k → Fin G.nE) (R : (Fin k → Bool) → Bool),
        IsParsimonious G T ext (fun x => R x = true) ∧
        (Finset.univ.filter (fun x => R x = true)).card = n ∧
        2 ≤ s ∧ b ≤ s ∧ G.nE < s ∧ G.nV ≤ s^L ∧
        G.maxDeg ≤ Nat.ceil ((s : ℝ)^((9 : ℝ)/10)) ∧
        s+w.length ≤ L * blockCount b * b ∧ s+w.length ≤ L*(b+1)^L ∧
        make w = encodeBTNInstance w G s s 1 ∧
        ∀ (v : Fin G.nV) (a : Fin (G.deg v) → Bool),
          let z := encodePortQuery w v.val (List.ofFn a)
          z.length ≤ L*(s+w.length+1)^L ∧
          port z = encodeNatListBin [if T v a then 1 else 0] := by sorry
