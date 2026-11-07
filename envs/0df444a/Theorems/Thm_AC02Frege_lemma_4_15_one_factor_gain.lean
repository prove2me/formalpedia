-- Prove2me | Theorems.Thm_AC02Frege_lemma_4_15_one_factor_gain
-- name    : AC02Frege.lemma_4_15_one_factor_gain
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:51:39.346376+00:00
-- url     : https://prove2.me/theorems/0b2302f3-456e-446b-a56f-003ab2373441
-- title:
--   Lemma 4.15 — one-factor gain with coefficient-degree loss
-- statement:
--   Let $\ell$ be odd, and consider a line with multilinear polynomials $u_1,\dots,u_s$ of degree at most $r$ and an intermediate approximator $P$. Suppose $K\ge r$ and $Q+\deg_xP+3r\le D$. Then some factor $q=1+\sum_ia_iu_i$, $a_i\in\mathbb F_2$, satisfies
--   $$
--   c_{Pq}(K)\ \le\ c_P(K)-\tfrac12c_P(K-r)+E_K+\tfrac12E_{K-r}.
--   $$
--
--   Appending a good Razborov–Smolensky factor removes half of the error conditions visible at degree $K-r$, up to the dimensions lost to the restriction $\beta\le Q$.
--
--   Differences from the source:
--   - encoding: ℓ odd, m = (ℓ − 1)/2 (standing assumption of §4) → hypothesis Odd ℓ, m = ℓ / 2; reason: same instances
--   - encoding: polynomials over F2 identified with functions on the cube; products of functions → MvPolynomial over ZMod 2; products multilinearized by ML (membership in Ĉ_D and β depend only on ML p); reason: Definition 2.1 identifies a function with its multilinear polynomial; no instance changes
--   - generalization: P an intermediate approximator → every multilinear P; reason: the statement and its proof use only deg_x P; specializes to the source
--   - encoding: a line with polynomials u_1, …, u_s; c_P(j) → u : Fin s → multilinear polynomials of degree ≤ r; M_N(j) − finrank of the span of Z_P(j); reason: Definition 4.14; same values
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Lemma 4.15, (24), p.25; proof App. B.2, pp.44–45

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_PC
import Definitions.Def_AC02Frege_lift
import Definitions.Def_AC02Frege_majorityExpansion
import Definitions.Def_AC02Frege_rankCounts

namespace AC02Frege

open MvPolynomial LiftSAParity

/-- Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret, *Progress on AC0[2]-Frege Lower Bounds*, manuscript (sha256 88d149fa…), Lemma 4.15, (24), p.25 (one-factor gain with coefficient-degree loss): for a line with
polynomials `u_1, …, u_s` of degree at most `r` and an intermediate approximator `P`, if
`K ≥ r` and `Q + deg_x P + 3r ≤ D` then some factor `q = 1 + Σ_i a_i u_i`, `a_i ∈ 𝔽₂`, satisfies
`c_{Pq}(K) ≤ c_P(K) − ½ c_P(K − r) + E_K + ½ E_{K−r}`.

**Formalization Note** `ℓ` odd; `u_i` and `P` multilinear; `Pq` is the product of functions.
Stated for every multilinear `P` (the proof uses only `deg_x P`). -/
theorem lemma_4_15_one_factor_gain {n ℓ : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n)) (D Q K r s : ℕ)
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (hu : ∀ i, IsMultilinear (u i) ∧ (u i).totalDegree ≤ r)
    (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hP : IsMultilinear P)
    (hrK : r ≤ K) (hD : Q + P.totalDegree + 3 * r ≤ D) :
    ∃ a : Fin s → ZMod 2,
      (cErr F ℓ D K (P * (1 + ∑ i, a i • u i)) u : ℝ) ≤
        (cErr F ℓ D K P u : ℝ) - (1 / 2) * (cErr F ℓ D (K - r) P u : ℝ)
          + (Eexcl n ℓ Q K : ℝ) + (1 / 2) * (Eexcl n ℓ Q (K - r) : ℝ) := by sorry

end AC02Frege
