-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_lemma_20
-- name    : ChvatalOneHard398.SAT.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:45:26.412107+00:00
-- url     : https://prove2.me/theorems/45b4eb86-b9de-4239-aff5-fb8e8170bdd7
-- title:
--   Lemma 20 — binary residue arithmetic
-- statement:
--   Let $X_0$ be a functional formulation, $u_1,\ldots,u_k$ any of its variables, $k\ge1$, $\alpha_i\ge0$ integer weights, $K\ge1$, and $L$ the smallest integer with $2^L\ge2K$. The concrete arithmetic template extends $X_0$ without changing free variables or multiple-choice constraints. It appends at most $6kL$ gates, each with at most three inputs and two outputs, and output fixings. It returns $L$ residue outputs $\rho_l$ and an integral linear function $\kappa$, satisfying
--
--   $$\sum_i\alpha_i x_{u_i}=K\kappa(x)+\sum_{l=0}^{L-1}2^l x_{\rho_l}\qquad(x\in X).$$
--
--   Every integral point of $X_0$ has exactly one integral extension in $X$. In that extension the residue outputs are the binary digits of $(\sum_i\alpha_i x_{u_i})\bmod K$. The template is polynomial-time computable from the binary weights and modulus. This retains the identity on every fractional point as well as the unique integral-extension property.
--
--   Differences from the source:
--   - encoding: deterministic polynomial time in structured bit size → TM2 polynomial time with fixed, dimension-prefixed, length-framed binary encodings; reason: these encodings are injective and have length linear in the corresponding bit size
--   - reading: time polynomial in k,log K,log(1+max α), with no X₀-size term → polynomial-time construction of a template on k abstract inputs, followed by substitution into X₀; reason: the proof computes precisely such a template; writing existing variable names is separated from the printed parameter bound
--   - encoding: O(kL) new functional constraints → at most 6kL new gates; reason: p.22 counts 3kL+k+2 gates and k,L≥1 imply 3kL+k+2≤6kL
--   - encoding: nonnegative integer weights, integral linear quotient, and binary residues → natural weights, integer coefficient lists, and explicit digit coordinates; reason: the source weights are exactly the natural numbers; floor extracts the already integral weighted sum without changing it
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.21, Lemma 20; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Encoding

namespace ChvatalOneHard398.SAT
open CombOpt.ChvatalRank

theorem lemma_20 :
    PolyTime encResidueInput encResidueResult (fun a => residueTemplate a.1 a.2) ∧
    ∀ (X0 : Functional) (u weights : List ℕ) (K : ℕ),
      X0.Valid → 1 ≤ weights.length → u.length = weights.length →
      (∀ v ∈ u, v < X0.dim) → 1 ≤ K →
      let z := extendResidue X0 u weights K
      let L := residueBits K
      z.model.Valid ∧ z.model.free = X0.free ∧ z.model.choices = X0.choices ∧
      z.model.gates.take X0.gates.length = X0.gates ∧
      z.model.fixings.take X0.fixings.length = X0.fixings ∧
      z.model.gates.length ≤ X0.gates.length + 6 * weights.length * L ∧
      (∀ g ∈ z.model.gates.drop X0.gates.length, g.inputs.length ≤ 3 ∧ g.outputs ≤ 2) ∧
      z.digits.length = L ∧ (∀ rho ∈ z.digits, rho ∈ z.model.outputIDs) ∧
      (∀ x ∈ functionalPoly z.model,
        ((List.range weights.length).map (fun i => ((weights[i]! : ℕ) : ℝ)*coord x u[i]!)).sum =
          (K : ℝ)*evalLinear z.quotient x +
            ((List.range L).map (fun l => (2 : ℝ)^l * coord x z.digits[l]!)).sum) ∧
      (∀ x0 ∈ functionalPoly X0, IsIntegralVector x0 →
        (∃! x : Fin z.model.dim → ℝ,
          x ∈ functionalPoly z.model ∧ IsIntegralVector x ∧ Extends x x0) ∧
        ∀ x ∈ functionalPoly z.model, IsIntegralVector x → Extends x x0 →
          ∀ l < L, coord x z.digits[l]! =
            if Nat.testBit
                (⌊((List.range weights.length).map (fun i =>
                  ((weights[i]! : ℕ) : ℝ)*coord x0 u[i]!)).sum⌋ % (K : ℤ)).toNat l
            then 1 else 0) := by sorry

end ChvatalOneHard398.SAT
