-- Prove2me | Theorems.Thm_ExtremalForrelation_Nonadaptive_lemma_2
-- name    : ExtremalForrelation.Nonadaptive.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:40.723483+00:00
-- url     : https://prove2.me/theorems/7d681321-bafb-46ef-b0b9-7c6d3c1c531b
-- title:
--   Lemma 2 — character sum over a coset
-- statement:
--   Throughout, $n$ is a multiple of $4$, $m=n/2$ and $M=2^m$ (the paper's standing notation, p. 3).
--
--   Let $W$ be a subspace of $\mathbb F_2^n$, $C$ a coset of $W$, $c\in C$, and $v\in\mathbb F_2^n$. Then
--   $$\sum_{x\in C}(-1)^{\langle x,v\rangle}=\begin{cases}(-1)^{\langle c,v\rangle}\,|W|, & v\in W^\perp,\\ 0, & \text{otherwise.}\end{cases}$$
--
--   This is the basic character sum used in every Fourier computation of the paper (Lemma 5).
--
--   Differences from the source:
--   - encoding: a coset C of V and c ∈ C → the coset is the class of c in the quotient by W; the sum runs over the x with the same class; reason: every coset containing c is c + W
-- source:
--   Clément Canonne, Kenny Chen, Julian Mestre, STOC 2027 submission #61 (October 2026), Lemma 2, p. 8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/61.pdf

import Mathlib
import Definitions.Def_ExtremalForrelation_Nonadaptive_Pinning
import Definitions.Def_ExtremalForrelation_Nonadaptive_Algorithm

open Classical

namespace ExtremalForrelation.Nonadaptive

/-- Lemma 2 (p. 8). For a subspace `W` of `𝔽₂ⁿ`, a coset `C = c + W` and `v ∈ 𝔽₂ⁿ`,
`∑_{x ∈ C} (−1)^{⟨x,v⟩} = (−1)^{⟨c,v⟩} |W|` if `v ∈ W^⊥`, and `0` otherwise. -/
theorem lemma_2 {n : ℕ} (hn : 4 ∣ n) (W : Submodule (ZMod 2) (V n)) (c v : V n) :
    ∑ x ∈ Finset.univ.filter (fun x : V n =>
        (Submodule.Quotient.mk x : V n ⧸ W) = Submodule.Quotient.mk c),
      (-1 : ℝ) ^ (dot x v).val =
    if v ∈ orth W then (-1 : ℝ) ^ (dot c v).val * (Nat.card W : ℝ) else 0 := by sorry

end ExtremalForrelation.Nonadaptive
