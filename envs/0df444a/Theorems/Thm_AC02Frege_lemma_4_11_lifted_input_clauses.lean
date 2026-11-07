-- Prove2me | Theorems.Thm_AC02Frege_lemma_4_11_lifted_input_clauses
-- name    : AC02Frege.lemma_4_11_lifted_input_clauses
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:50:45.288875+00:00
-- url     : https://prove2.me/theorems/336b141c-bff1-4d89-b26c-c496e929ab5e
-- title:
--   Lemma 4.11 — lifted input clauses
-- statement:
--   Let $\ell$ be odd, $F$ a CNF and $G=F\circ\mathrm{Maj}_\ell$. Let $1+a(x)=1$ be the encoding of an input clause $C$ of $G$, with $a=\overline C=\prod_{\lambda\in C}(1+\lambda(x))$ its complement. If $\beta(f)\le Q$ and $Q+2w(F)\le D$, then
--   $$
--   fa\in\widehat C_D .
--   $$
--
--   This replaces, for the lifted formula, the fact that the complements of the input clauses lie in $C_D$.
--
--   Differences from the source:
--   - encoding: ℓ odd, m = (ℓ − 1)/2 (standing assumption of §4) → hypothesis Odd ℓ, m = ℓ / 2; reason: same instances
--   - encoding: polynomials over F2 identified with functions on the cube; products of functions → MvPolynomial over ZMod 2; products multilinearized by ML (membership in Ĉ_D and β depend only on ML p); reason: Definition 2.1 identifies a function with its multilinear polynomial; no instance changes
--   - encoding: w(F), the width of F → width F = the largest clause size of F (0 for the empty CNF); reason: same values
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Lemma 4.11, p.23

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_PC
import Definitions.Def_AC02Frege_lift
import Definitions.Def_AC02Frege_majorityExpansion

namespace AC02Frege

open MvPolynomial LiftSAParity

/-- Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret, *Progress on AC0[2]-Frege Lower Bounds*, manuscript (sha256 88d149fa…), Lemma 4.11, p.23 (lifted input clauses): let `1 + a(x) = 1` be the encoding of an input
clause `C` of `G = F ∘ Maj_ℓ`, with `a = C̄` its complement. If `β(f) ≤ Q` and
`Q + 2w(F) ≤ D`, then `fa ∈ Ĉ_D`.

**Formalization Note** `ℓ` is odd; `C̄ = ∏_{λ ∈ C} (1 + λ(x))` is `clauseCompl C`; `w(F)` is
`width F`; `fa` is the product of functions. -/
theorem lemma_4_11_lifted_input_clauses {n ℓ : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n)) (D Q : ℕ)
    (C : Clause (Fin n × Fin ℓ)) (hC : C ∈ lift F ℓ) (f : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (hf : coeffDeg f ≤ (Q : WithBot ℕ)) (hD : Q + 2 * width F ≤ D) :
    f * clauseCompl C ∈ CHat F ℓ D := by sorry

end AC02Frege
