-- Prove2me | Theorems.Thm_AC02Frege_lemma_4_16_degree_comparison
-- name    : AC02Frege.lemma_4_16_degree_comparison
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:51:17.625879+00:00
-- url     : https://prove2.me/theorems/cef18fde-1839-4198-a87e-cc4657bbefa1
-- title:
--   Lemma 4.16 — degree comparison with coefficient-degree loss
-- statement:
--   Let $\ell$ be odd, $N=n\ell$, and consider a line with multilinear polynomials $u_1,\dots,u_s$ of degree at most $r$ and an intermediate approximator $P$. Suppose $r\le K<N/2$ and $Q+\deg_xP+r+1\le D$. Then
--   $$
--   c_P(K-r)\ \ge\ \frac{M_N(K-r)}{M_N(K)}\,c_P(K)-N^2\varepsilon M_N(K-r).
--   $$
--
--   The gain of one factor is measured at degree $K-r$; this lemma compares it with the count at degree $K$, paying an additive loss for the restriction to $W_Q$.
--
--   Differences from the source:
--   - encoding: ℓ odd, m = (ℓ − 1)/2 (standing assumption of §4) → hypothesis Odd ℓ, m = ℓ / 2; reason: same instances
--   - encoding: polynomials over F2 identified with functions on the cube; products of functions → MvPolynomial over ZMod 2; products multilinearized by ML (membership in Ĉ_D and β depend only on ML p); reason: Definition 2.1 identifies a function with its multilinear polynomial; no instance changes
--   - generalization: P an intermediate approximator (a product of Razborov–Smolensky factors) → every multilinear P; reason: the statement and its proof use only deg_x P; specializes to the source
--   - encoding: a line of Res(PC_r) with polynomials u_1, …, u_s → u : Fin s → multilinear polynomials of degree ≤ r; reason: the lemma concerns one line
--   - encoding: c_P(j) = rank T_{P,j} = M_N(j) − dim Z_P(j); K < N/2 → M_N(j) − finrank of the span of Z_P(j), Z_P(j) defined by membership in Ĉ_D; 2K < N; reason: Definition 4.14 gives both expressions; same values
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Lemma 4.16, (25), p.25; proof App. B.1, pp.43–44

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_PC
import Definitions.Def_AC02Frege_lift
import Definitions.Def_AC02Frege_majorityExpansion
import Definitions.Def_AC02Frege_rankCounts

namespace AC02Frege

open MvPolynomial LiftSAParity

/-- Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret, *Progress on AC0[2]-Frege Lower Bounds*, manuscript (sha256 88d149fa…), Lemma 4.16, (25), p.25 (degree comparison with coefficient-degree loss): for a line with
polynomials `u_1, …, u_s` of degree at most `r` and an intermediate approximator `P`, if
`r ≤ K < N/2` and `Q + deg_x P + r + 1 ≤ D` then
`c_P(K − r) ≥ M_N(K − r)/M_N(K) · c_P(K) − N² ε M_N(K − r)`.

**Formalization Note** `ℓ` odd, `N = nℓ`; `u_i` and `P` multilinear; `ε = epsExcl n ℓ Q K`.
Stated for every multilinear `P`, not only products of Razborov–Smolensky factors (the proof
uses only `deg_x P`). -/
theorem lemma_4_16_degree_comparison {n ℓ : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n)) (D Q K r s : ℕ)
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (hu : ∀ i, IsMultilinear (u i) ∧ (u i).totalDegree ≤ r)
    (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hP : IsMultilinear P)
    (hrK : r ≤ K) (hKN : 2 * K < n * ℓ) (hD : Q + P.totalDegree + r + 1 ≤ D) :
    (monoCount (n * ℓ) (K - r) : ℝ) / (monoCount (n * ℓ) K : ℝ) * (cErr F ℓ D K P u : ℝ)
        - ((n * ℓ : ℕ) : ℝ) ^ 2 * epsExcl n ℓ Q K * (monoCount (n * ℓ) (K - r) : ℝ)
      ≤ (cErr F ℓ D (K - r) P u : ℝ) := by sorry

end AC02Frege
