-- Prove2me | Theorems.Thm_DeMorganApprox_Main_claim_4_1_1
-- name    : DeMorganApprox.Main.claim_4_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:07.668015+00:00
-- url     : https://prove2.me/theorems/3938afd3-6648-4fb7-b00b-870c678af886
-- title:
--   Claim 4.1.1 — ‖o⊤ M̃(x)^j o‖₁ ≤ 1 for every j ≥ 0
-- statement:
--   Let a span program have unit target $\tau$ and full column matrix $V$ with $\|\operatorname{abs}(V)\|\le K$, let $S\ge1$, and let $\widetilde M(x)=M(x)/c_{\rm norm}$ be the normalized symbolic matrix of the proof of Lemma 4.1, a matrix of polynomials in $x_1,\dots,x_m$. For the proof's choice of the constant $c_{\rm norm}$, for every integer $j\ge0$,
--   $$\left\|o^\top\widetilde M(x)^jo\right\|_1\le1,$$
--   where $\|\cdot\|_1$ is the coefficient ℓ1-norm taken before multilinearization.
--
--   With Claim 4.1.2 this bounds the coefficient norm of $o^\top\Psi(\widetilde M(x))o$ by $\sum_j|\alpha_j|$.
--
--   Differences from the source:
--   - generalization: a vector-form span program computing f with balanced witness bound S, inside the proof of Lemma 4.1 → any raw span program with unit target and ‖abs(V)‖ ≤ K, and any S ≥ 1; reason: the claim's proof uses only ‖τ‖ = 1, ‖abs(V)‖ ≤ K and S ≥ 1; it specializes to the source's program
--   - reading: our choice of c_norm (a sufficiently large absolute constant) → ∃ c₀ depending only on K such that the bound holds for every c_norm ≥ c₀; reason: the source fixes c_norm large enough given the O(1) bound on ‖abs(V)‖
--   - encoding: coefficient ℓ1-norm of the entry o⊤M̃(x)^j o, before multilinearization → coeffL1 of the (Sum.inl (), Sum.inl ()) entry of the matrix power (scaledSymbolicMatrix P S cnorm)^j over MvPolynomial (Fin m) ℝ, with no reduction of xᵢ²; reason: the same polynomial and the same norm
--   - encoding: a real Euclidean space H with unit vectors and the entrywise absolute value abs(V) → the coordinate space ι → ℝ for a finite type ι with its standard basis; squared norms are sums of squares; reason: abs(V) is only defined relative to a fixed orthonormal basis, which the construction provides (leaf and helper coordinates); finitely many listed vectors span a finite-dimensional subspace
-- source:
--   Yichuan Wang, STOC 2027 submission #76 (October 2026), Claim 4.1.1, PDF p. 16 (printed p. 14), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/76.pdf; c_norm chosen on PDF pp. 12 and 16; M̃(x) on PDF p. 14

import Mathlib
import Definitions.Def_DeMorganApprox_Main_Extraction

namespace DeMorganApprox.Main

/-- Claim 4.1.1, PDF p. 16 (printed p. 14): `‖o⊤ M̃(x)^j o‖₁ ≤ 1`, coefficient norm taken
before multilinearization. `c₀` encodes "our choice of `c_norm`" and depends only on `K`. -/
theorem claim_4_1_1 (K : ℝ) (hK : 0 ≤ K) :
    ∃ c₀ : ℝ, ∀ cnorm : ℝ, c₀ ≤ cnorm →
      ∀ (m : ℕ) {ι J : Type} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]
        (P : SpanProgram m ι J), sqNorm P.target = 1 → AbsNormLE P.vec K →
        ∀ S : ℝ, 1 ≤ S → ∀ j : ℕ,
          coeffL1 ((scaledSymbolicMatrix P S cnorm ^ j) (Sum.inl ()) (Sum.inl ())) ≤ 1
    := by sorry

end DeMorganApprox.Main
