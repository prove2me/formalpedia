-- Prove2me | Theorems.Thm_BenignDegen_lemma_B_2
-- name    : BenignDegen.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:04.531246+00:00
-- url     : https://prove2.me/theorems/148e4244-36ce-47ee-82fe-19a62dac77f7
-- title:
--   Lemma B.2 — every certificate in $\mathcal S_\star$ has trace $f_\emptyset-f_\star$, so $\mathcal S_\star$ is compact
-- statement:
--   Let $1\le d\le n$, $f$ a square-free polynomial and $f_\star\in\mathbb R$. Every PSD Gram matrix $S$ with $b_d(x)^\top Sb_d(x)\equiv f-f_\star\pmod{I_B}$ satisfies
--
--   $$
--   \operatorname{tr}S=f_\emptyset-f_\star ,
--   $$
--
--   and consequently the set $\mathcal S_\star$ of such $S$ (2.4) is compact. In the paper $f_\star$ is the value of an exact relaxation; compactness of $\mathcal S_\star$ is the compactness half of Assumption 3.1 in the Boolean instantiation.
--
--   Differences from the source:
--   - encoding: square-free f, I_d, {±1}ⁿ, '≡ (mod I_B)' → coefficient function Finset (Fin n) → ℝ, {T : Finset (Fin n) // T.card ≤ d}, Fin n → ℤˣ, equality of square-free coefficients through G_d (B.2); reason: the same objects; I_d = {T : |T| ≤ min{d, n}} because |T| ≤ n always
--   - generalization: the relaxation at order d is exact with value f⋆ → every real f⋆ (no exactness hypothesis); reason: the trace identity is the ∅-coefficient of the congruence and compactness holds for every f⋆; the exact value is one instance
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, Appendix B, Lemma B.2, p.15

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Convergence
import Definitions.Def_BenignDegen_Algorithms
import Definitions.Def_BenignDegen_Boolean
open SunNLSDP.Equiv Matrix Filter Topology
open scoped RealInnerProductSpace Pointwise

namespace BenignDegen

/-- Lemma B.2 (trace identity and compactness), Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*, arXiv:2610.20270v1, p.15.
Every Gram certificate `S ⪰ 0` with `b_d(x)^⊤ S b_d(x) ≡ f − f_⋆ (mod I_B)` has
`tr S = f_∅ − f_⋆`; consequently the set `S_⋆` of (2.4) is compact.

**Formalization Note** Stated for every real `f_⋆` (in the paper `f_⋆` is the exact value of the
relaxation); the set `S_⋆` is `gramCerts n d f f_⋆`. -/
theorem lemma_B_2 (n d : ℕ) (hd : 1 ≤ d) (hdn : d ≤ n) (f : Finset (Fin n) → ℝ) (fstar : ℝ) :
    (∀ S ∈ gramCerts n d f fstar, Matrix.trace S.toMat = f ∅ - fstar) ∧
    IsCompact (gramCerts n d f fstar) := by sorry

end BenignDegen
