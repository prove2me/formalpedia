-- Prove2me | Theorems.Thm_DHRUniq_nielsen_theorem
-- name    : DHRUniq.nielsen_theorem
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:34:34.415583+00:00
-- url     : https://prove2.me/theorems/3237fe76-8462-4876-90c7-d03f83717a3c
-- title:
--   Theorem 7 (Nielsen): LQCC convertibility of pure states is majorization
-- statement:
--   Let $\mathcal H^A$, $\mathcal H^B$ be Hilbert spaces and let $(|\chi_m\rangle)_{m=1}^M$, $(|\kappa_m\rangle)_{m=1}^M$ be orthonormal bases of $\mathcal H^A$ and $\mathcal H^B$. Let
--
--   $$
--   |\Psi\rangle=\sum_{m=1}^M\sqrt{p_m}\,|\chi_m\kappa_m\rangle,\qquad |\Phi\rangle=\sum_{m=1}^M\sqrt{q_m}\,|\chi_m\kappa_m\rangle
--   $$
--
--   be Schmidt decompositions of normalized vectors with $p_1\ge\dots\ge p_M$ and $q_1\ge\dots\ge q_M$. Then $|\Psi\rangle\langle\Psi|$ can be converted into $|\Phi\rangle\langle\Phi|$ by LQCC operations if and only if $(q_i)$ majorizes $(p_i)$.
--
--   This criterion decides which single-copy pure-state conversions are possible, and every comparison of pure states in the paper rests on it.
--
--   Differences from the source:
--   - encoding: finite-dimensional Hilbert spaces H^A, H^B → ℂ^a, ℂ^b for finite index types a, b with the standard basis; reason: every finite-dimensional Hilbert space is unitarily isomorphic to such a space
--   - encoding: orthonormal bases (χ_m), (κ_m) with M elements → orthonormal families of M elements with card a = card b = M; reason: an orthonormal family of dim-many vectors is a basis
--   - encoding: converted by LQCC operations → there is one map Λ with IsLQCC Λ and Λ(|Ψ⟩⟨Ψ|) = |Φ⟩⟨Φ|; reason: the class of Definition 4 is closed under composition (p. 6), so a sequence of operations is one operation
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, Theorem 7 (Nielsen), p. 6

import Mathlib
import Definitions.Def_DHRUniq_IsUnitVec
import Definitions.Def_DHRUniq_IsSchmidtDecomp
import Definitions.Def_DHRUniq_IsLQCC
import Definitions.Def_DHRUniq_Majorizes
import Definitions.Def_ObliviousRSP_pureState

open ObliviousRSP (pureState)

namespace DHRUniq

/-- **Theorem 7 (Nielsen)** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, Theorem 7, p. 6, with Definition 6). Let `(|χ_m⟩)_{m=1}^M` and
`(|κ_m⟩)_{m=1}^M` be orthonormal bases of `H^A` and `H^B`, and let
`|Ψ⟩ = ∑_m √p_m |χ_m κ_m⟩`, `|Φ⟩ = ∑_m √q_m |χ_m κ_m⟩` be Schmidt decompositions of normalized
vectors with `p_1 ≥ … ≥ p_M` and `q_1 ≥ … ≥ q_M`. Then `|Ψ⟩⟨Ψ|` can be converted into `|Φ⟩⟨Φ|` by
LQCC operations if and only if `(q_i)` majorises `(p_i)`.

**Formalization Note** The families are bases because they have `M = dim` elements (`hcardA`,
`hcardB`). "Converted by LQCC operations" is the existence of one LQCC map `H^A ⊗ H^B → H^A ⊗ H^B`:
the class of Definition 4 contains the composition of the paper's `Λ_1 ∘ … ∘ Λ_N`. Both directions
are stated. -/
theorem nielsen_theorem {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (M : ℕ) (hcardA : Fintype.card a = M) (hcardB : Fintype.card b = M)
    (χ : Fin M → a → ℂ) (κ : Fin M → b → ℂ) (p q : Fin M → ℝ) (Ψ Φ : a × b → ℂ)
    (hΨ : IsUnitVec Ψ) (hΦ : IsUnitVec Φ)
    (hp : IsSchmidtDecomp Ψ p χ κ) (hq : IsSchmidtDecomp Φ q χ κ)
    (hpa : Antitone p) (hqa : Antitone q) :
    (∃ Λ : Matrix (a × b) (a × b) ℂ → Matrix (a × b) (a × b) ℂ,
        IsLQCC Λ ∧ Λ (pureState Ψ) = pureState Φ) ↔
      Majorizes (List.ofFn q) (List.ofFn p) := by sorry

end DHRUniq
