-- Prove2me | Theorems.Thm_BMPV1173_Verification_theorem_2_10
-- name    : BMPV1173.Verification.theorem_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:06:59.273366+00:00
-- url     : https://prove2.me/theorems/72c20be8-87b7-48bc-8637-3337f8155a0f
-- title:
--   Theorem 2.10 — MNRS search on a Johnson graph
-- statement:
--   Consider the Johnson walk on the $r$-subsets of a known $n$-element universe, with $n\ge3$ and $1\le r\le n/2$. Whenever marked states exist, suppose all subsets containing some distinguished element are marked. If coherent uniform setup with the actual maintained data costs $S$ queries, a coherent neighboring-state update costs $U$, and checking a state costs $C$, then marked-state detection has query cost
--   $$\widetilde O\!\left(S+\sqrt n\,U+\sqrt{n/r}\,C\right).$$
--   The conclusion supplies one actual circuit with inverse-polynomial error on every promised input. Setup, update and checking are explicitly represented quantum operations, with the accuracy exponent chosen before all instances. The data and marking predicates may depend on the unknown oracle input; the operation circuits cannot. The checker is supplied with the subset and its maintained data and coherently writes the marked bit while restoring that data.
--
--   Differences from the source:
--   - encoding: polynomial-size parameters and inverse-polynomial subroutine error → fixed polynomial envelope and an existential required accuracy exponent before all instances; reason: this makes the section standing convention explicit; constants depend only on fixed envelopes and requested error exponents
--   - encoding: coherent setup and walk update → clean norm approximation on arbitrary admissible superpositions, including sampled data and a reset scratch register; reason: this states the coherent operations required by the source error convention, including implicit member selection
--   - encoding: r-subsets and their data → uniform setup on (I,I,data(I)) and a clean swap (I,J,data(I)) to (J,I,data(J)) for Johnson neighbors; reason: copying the known subset label and preparing a uniform neighbor in a known universe are query free; the data replacement remains charged
--   - encoding: checking whether a walk state with its maintained data is marked → a clean coherent XOR of the marked bit into an answer qubit, supplied with the subset and its actual maintained data; reason: the source checker can inspect acquired data for free; compute-copy-uncompute after amplification gives this clean operation with constant query overhead absorbed in soft-O
--   - generalization: the section convention that index sets have polynomial size in the ambient input parameter → an arbitrary finite input-oracle address type, with polynomial bounds on the candidate and resource parameters explicitly listed in the theorem; reason: the search bounds count entry queries and depend on candidate sizes and subroutine costs, not the number of input-oracle addresses; polynomial-size source oracles are included
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, Theorem 2.10, printed p.16 = PDF p.16.

import Definitions.Def_BMPV1173_Verification_SearchTasks

namespace BMPV1173.Verification

/-- Johnson walk search, Theorem 2.10, p.16. Setup is uniform with its
actual data; update coherently swaps neighboring states while replacing the data.
The accuracy exponent e absorbs the source's inverse-polynomial error convention. -/
theorem theorem_2_10 (c : ℝ) (hc : 0 < c) (b : ℕ) (hb : 1 ≤ b) :
    ∃ (H : ℝ) (k e : ℕ), 0 < H ∧
    ∀ (n r S U C : ℕ), 3 ≤ n → 1 ≤ r → 2*r ≤ n →
      S ≤ n^b → U ≤ n^b → C ≤ n^b →
    ∀ (ι δ : Type) [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
      (q0 : ι) (zero : δ) (D : Set (ι → Bool))
      (data : (ι → Bool) → Finset (Fin n) → δ)
      (marked : (ι → Bool) → Finset (Fin n) → Prop),
      MarkingGuarantee r D marked →
      HasCoherentMap q0 D (fun _ (_ : Unit) => True)
        (fun _ _ => QAlgorithms.ket (∅,∅,zero))
        (fun x _ => walkSetup n r data x) ((n : ℝ)^(-(e : ℝ))) S →
      HasCoherentMap q0 D (fun _ (IJ : Finset (Fin n) × Finset (Fin n)) => johnsonAdjacent r IJ.1 IJ.2)
        (fun x IJ => QAlgorithms.ket (IJ.1,IJ.2,data x IJ.1))
        (fun x IJ => QAlgorithms.ket (IJ.2,IJ.1,data x IJ.2)) ((n : ℝ)^(-(e : ℝ))) U →
      HasCoherentMap q0 D
        (fun _ (Ib : Finset (Fin n) × Bool) => Ib.1 ∈ rSubsets n r)
        (fun x Ib => QAlgorithms.ket ((Ib.1,Ib.1,data x Ib.1),Ib.2))
        (fun x (Ib : Finset (Fin n) × Bool) => by
          classical
          exact QAlgorithms.ket ((Ib.1,Ib.1,data x Ib.1),xor Ib.2 (decide (marked x Ib.1))))
        ((n : ℝ)^(-(e : ℝ))) C →
      ∃ T : ℕ,
        HasDecision D (fun x => by classical exact decide (∃ I ∈ rSubsets n r, marked x I))
          ((n : ℝ)^(-c)) T ∧
        (T : ℝ) ≤ H*((S : ℝ)+Real.sqrt (n : ℝ)*U+Real.sqrt ((n : ℝ)/r)*C)*
          (1+Real.log (n : ℝ))^k := by sorry

end BMPV1173.Verification
