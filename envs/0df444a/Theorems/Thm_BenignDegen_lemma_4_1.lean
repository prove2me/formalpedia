-- Prove2me | Theorems.Thm_BenignDegen_lemma_4_1
-- name    : BenignDegen.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:03.970962+00:00
-- url     : https://prove2.me/theorems/e1c815c8-2223-4922-a4fc-0dcf1824b67b
-- title:
--   Lemma 4.1 — Boolean subspace geometry: $\mathbb S(V)^\perp=\{qv^\top+vq^\top\}$, $\mathcal T_d\cap\mathbb S(V)^\perp=\{0\}$, $\mathbb S(V)\cap\mathcal R_d=\mathbb S(V)\cap\mathcal H_d^\perp$
-- statement:
--   Let $1\le d\le n$, $x_\star\in\{\pm1\}^n$, $q=b_d(x_\star)/\sqrt N$ and $V=q^\perp$. Then
--
--   $$
--   \mathbb S(V)^\perp=\{qv^\top+vq^\top:v\in\mathbb R^N\},\qquad \mathcal T_d\cap\mathbb S(V)^\perp=\{0\},\qquad \mathbb S(V)\cap\mathcal R_d=\mathbb S(V)\cap\mathcal H_d^\perp,
--   $$
--
--   and $\mathcal H_d=\operatorname{span}\{I_N\}\oplus\mathcal T_d$. In the Boolean instantiation the dual direction space is $\mathcal L=\mathbb S(V)\cap\mathcal R_d$, so the last identity says $\mathcal L=\mathbb S(V)\cap\mathcal H_d^\perp$: no consistency direction lies in $\mathbb S(V)^\perp$, and inside $\mathbb S(V)$ the equality row space and the Gram-map kernel agree.
--
--   Differences from the source:
--   - encoding: square-free f, I_d, {±1}ⁿ, '≡ (mod I_B)' → coefficient function Finset (Fin n) → ℝ, {T : Finset (Fin n) // T.card ≤ d}, Fin n → ℤˣ, equality of square-free coefficients through G_d (B.2); reason: the same objects; I_d = {T : |T| ≤ min{d, n}} because |T| ≤ n always
--   - generalization: q = b_d(x⋆)/√N for the unique minimizer x⋆ of a uniquely rank-one exact order → q = b_d(x)/√N for every cube point x; reason: the proof uses only q_A = ±N^{−1/2} and (uu^⊤)_{A,B} = x^{A△B}, true for every cube point
--   - encoding: L = S(V) ∩ R_d (L := R ∩ S(V) with R = ran A_d^* = R_d); H_d = span{I_N} ⊕ T_d → S(V) ⊓ R_d = S(V) ⊓ H_d^⊥; H_d = span{I_N} ⊔ T_d with the two summands disjoint; reason: the same identities, R = R_d by Proposition B.1
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, §4.1, Lemma 4.1, (4.1)–(4.3), p.9

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Convergence
import Definitions.Def_BenignDegen_Algorithms
import Definitions.Def_BenignDegen_Boolean
open SunNLSDP.Equiv Matrix Filter Topology
open scoped RealInnerProductSpace Pointwise

namespace BenignDegen

/-- Lemma 4.1 (Boolean subspace geometry), Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*, arXiv:2610.20270v1, p.9.
With `q = b_d(x_⋆)/√N` and `V = q^⊥`: (4.1) `S(V)^⊥ = {qv^⊤ + vq^⊤ : v ∈ ℝ^N}`;
(4.2) `T_d ∩ S(V)^⊥ = {0}`; (4.3) `S(V) ∩ R_d = S(V) ∩ H_d^⊥` (both equal to `L` of (3.3)) and
`H_d = span{I_N} ⊕ T_d`.

**Formalization Note** Stated for every cube point `x_⋆ ∈ {±1}ⁿ`. -/
theorem lemma_4_1 (n d : ℕ) (hd : 1 ≤ d) (hdn : d ≤ n) (x : Fin n → ℤˣ) :
    ((supported (Vq n d x))ᗮ : Set (SymMat (Idx n d))) =
      Set.range (fun v : Idx n d → ℝ => SymMat.ofMat
        (vecMulVec (WithLp.ofLp (qvec n d x)) v + vecMulVec v (WithLp.ofLp (qvec n d x)))) ∧
    Td n d ⊓ (supported (Vq n d x))ᗮ = ⊥ ∧
    supported (Vq n d x) ⊓ Rd n d = supported (Vq n d x) ⊓ (Hd n d)ᗮ ∧
    Hd n d = Submodule.span ℝ {IdMat (Idx n d)} ⊔ Td n d ∧
    Disjoint (Submodule.span ℝ {IdMat (Idx n d)}) (Td n d) := by sorry

end BenignDegen
