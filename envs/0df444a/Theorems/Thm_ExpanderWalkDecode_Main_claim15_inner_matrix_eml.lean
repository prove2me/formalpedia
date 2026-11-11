-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_claim15_inner_matrix_eml
-- name    : ExpanderWalkDecode.Main.claim15_inner_matrix_eml
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:21:39.212944+00:00
-- url     : https://prove2.me/theorems/b6a03d93-62b7-4a54-9220-45aa5c93d9fb
-- title:
--   Claim 15 — inner matrix expander mixing lemma on $A\times B$
-- statement:
--   Let $A$ be a finite set and $B$ (the vertex set of) a $\lambda_B$-expander, and $f,g:A\times B\to\mathbb R^{D\times D}$. With $M_f(a)=\mathbb E_b[f(a,b)]$, $M_f=\mathbb E_{a,b}[f(a,b)]$ and $\sigma_f^2=\|\mathbb E_{a,b}[f(a,b)^{\mathsf T}f(a,b)]-M_f^{\mathsf T}M_f\|_{\mathrm{op}}$ (likewise for $g$),
--   $$\Big\|\mathbb E_{a,\,b\sim b'}\big[f(a,b)^{\mathsf T}g(a,b')-M_f(a)^{\mathsf T}M_g(a)\big]\Big\|_{\mathrm{op}}\le\lambda_B\,\sigma_f\,\sigma_g ,$$
--   where $a$ and $b$ are uniform and $b'$ is a uniform neighbour of $b$. The variance $\sigma_f$ is the global one.
--
--   The expansion parameter $\lambda_B$ is positive, as stipulated in §3.3.
--
--   Differences from the source:
--   - reading: A any set, with E_a → A a finite nonempty set with the uniform average; reason: the source's E_a is the uniform average; it is defined only for a finite set
--   - encoding: E_{b∼b′} → average over a uniform vertex and a uniform port of the rotation map of B; reason: same distribution of edges
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 24 (PDF p. 27), Appendix B.5, Claim 15; restated p. 21 (PDF p. 24)

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Graphs

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Claim 15 (Inner Matrix EML) (Appendix B.5, p. 24): let `A` be a finite set and `B` a
`λ_B`-expander; for `f, g : A × B → ℝ^{D×D}`,
`‖E_{a, b∼b′}[f(a,b)ᵀ g(a,b′) - M_f(a)ᵀ M_g(a)]‖_op ≤ λ_B σ_f σ_g`, where `M_f(a) = E_b f(a,b)`,
`M_f = E_{a,b} f(a,b)` and `σ_f² = ‖E_{a,b}[f(a,b)ᵀ f(a,b)] - M_fᵀ M_f‖_op`. -/
theorem claim15_inner_matrix_eml {A Bv P : Type} [Fintype A] [Nonempty A] [Fintype Bv] [Nonempty Bv]
    [Fintype P] [Nonempty P] {D : ℕ} (B : RotGraph Bv P) (lamB : ℝ) (hpos : 0 < lamB) (hB : B.IsExpander lamB)
    (f g : A → Bv → Matrix (Fin D) (Fin D) ℝ) :
    opNorm (avg fun abi : A × Bv × P =>
        (f abi.1 abi.2.1)ᵀ * g abi.1 (B.nbr abi.2.1 abi.2.2)
          - (avg fun b => f abi.1 b)ᵀ * avg fun b => g abi.1 b) ≤
      lamB * Real.sqrt (opNorm ((avg fun ab : A × Bv => (f ab.1 ab.2)ᵀ * f ab.1 ab.2)
          - (avg fun ab : A × Bv => f ab.1 ab.2)ᵀ * avg fun ab : A × Bv => f ab.1 ab.2))
        * Real.sqrt (opNorm ((avg fun ab : A × Bv => (g ab.1 ab.2)ᵀ * g ab.1 ab.2)
          - (avg fun ab : A × Bv => g ab.1 ab.2)ᵀ * avg fun ab : A × Bv => g ab.1 ab.2)) := by sorry

end ExpanderWalkDecode.Main
