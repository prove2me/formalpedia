-- Prove2me | Theorems.Thm_FermionModewise_clifford
-- name    : FermionModewise.clifford
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:32:29.141063+00:00
-- url     : https://prove2.me/theorems/52fd8c73-8391-4352-9576-89aadc86f51a
-- title:
--   The quadratures are Hermitian and the anticommutation relations are the Clifford algebra $\{\gamma_\alpha,\gamma_\beta\}=2\delta_{\alpha\beta}$
-- statement:
--   Let $(b_i)_{i\in\mu}$ be operators on a finite-dimensional space and $\gamma$ their quadratures (5). Then every $\gamma_\alpha$ is Hermitian, and the family $b$ satisfies the canonical anticommutation relations if and only if
--   $$\{\gamma_\alpha,\gamma_\beta\}=\gamma_\alpha\gamma_\beta+\gamma_\beta\gamma_\alpha=2\,\delta_{\alpha\beta}\,\mathbb 1\qquad\text{for all quadrature labels }\alpha,\beta. \tag{6}$$
--
--   This turns canonical transformations into real orthogonal transformations of the quadratures, which is how the whole argument proceeds.
--
--   Differences from the source:
--   - reading: the anticommutation relations are "a consequence of" (6) "satisfied by the γα" → both directions, CAR ⇔ (6); reason: the page asserts that the γα satisfy (6) and that the relations follow from it
--   - generalization: modes on the Fock space → operators on any finite-dimensional space; reason: the identities are algebraic, and the Fock space is an instance
--   - encoding: quadrature labels 2i−1, 2i → (i, 0), (i, 1); reason: relabelling only
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (5), p.3 and eq. (6), p.4

import Mathlib
import Definitions.Def_FermionModewise_IsCAR
import Definitions.Def_FermionModewise_majorana

open Matrix

namespace FermionModewise

/-- **Clifford relations of the quadratures** (Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (5),
p.3, and eq. (6), p.4): the quadratures `γ = majorana b` are Hermitian, and the anticommutation
relations of the modes `b` are equivalent to the Clifford algebra `{γ_α, γ_β} = 2 δ_αβ`.

**Formalization Note.** The page says the anticommutation relations are "a consequence of" (6)
satisfied by the `γ_α`; both directions are stated. Quadratures are indexed by `μ × Fin 2`
(see `majorana`). -/
theorem clifford {ι μ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq μ]
    (b : μ → Matrix ι ι ℂ) :
    (∀ p, (majorana b p)ᴴ = majorana b p) ∧
      (IsCAR b ↔ ∀ p q, majorana b p * majorana b q + majorana b q * majorana b p =
        (if p = q then (2 : ℂ) else 0) • (1 : Matrix ι ι ℂ)) := by sorry

end FermionModewise
