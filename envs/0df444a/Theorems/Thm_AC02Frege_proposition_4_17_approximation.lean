-- Prove2me | Theorems.Thm_AC02Frege_proposition_4_17_approximation
-- name    : AC02Frege.proposition_4_17_approximation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:51:44.336432+00:00
-- url     : https://prove2.me/theorems/64ef3971-19c1-4387-970d-168459e24b64
-- title:
--   Proposition 4.17 — the approximation estimate with coefficient-degree losses
-- statement:
--   Let $\ell$ be odd and $N=n\ell$. Suppose $t,r\ge1$, $r\le K<N/2$ and $Q+(t+2)r\le D$, and let $\eta=\tfrac12M_N(K-r)/M_N(K)$. For each line, with multilinear polynomials $u_1,\dots,u_s$ of degree at most $r$, there is an approximator $P_L=\prod_{\nu=1}^{t}\bigl(1+\sum_ia_{\nu i}u_i\bigr)$, $a_{\nu i}\in\mathbb F_2$, such that
--   $$
--   c_{P_L}(K)\ \le\ e^{-\eta t}\bigl(h+\varepsilon M_N(K)\bigr)+\frac{2N^2\varepsilon M_N(K)}{\eta}.
--   $$
--
--   The first term is the geometric decrease of the error conditions; the second is the accumulated leak from the coefficient-degree restriction.
--
--   Differences from the source:
--   - encoding: ℓ odd, m = (ℓ − 1)/2 (standing assumption of §4) → hypothesis Odd ℓ, m = ℓ / 2; reason: same instances
--   - encoding: polynomials over F2 identified with functions on the cube; products of functions → MvPolynomial over ZMod 2; products multilinearized by ML (membership in Ĉ_D and β depend only on ML p); reason: Definition 2.1 identifies a function with its multilinear polynomial; no instance changes
--   - encoding: for each line, an approximator built from t factors of the form 1 + Σ_i a_i u_i → for every family u : Fin s → multilinear polynomials of degree ≤ r there are a : Fin t → Fin s → ZMod 2 with P_L = ML ∏_ν (1 + Σ_i a ν i u_i); reason: Corollary 5.3 applies the proposition to such families; same content
--   - encoding: h, ε, η, c_P → hThresh, epsExcl, etaFrac, cErr (finrank of spans), real arithmetic; K < N/2 as 2K < N; reason: same values
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Proposition 4.17, (27), p.25; proof App. B.3, p.45

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_PC
import Definitions.Def_AC02Frege_lift
import Definitions.Def_AC02Frege_majorityExpansion
import Definitions.Def_AC02Frege_rankCounts

namespace AC02Frege

open MvPolynomial LiftSAParity

/-- Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret, *Progress on AC0[2]-Frege Lower Bounds*, manuscript (sha256 88d149fa…), Proposition 4.17, (27), p.25 (the approximation estimate with coefficient-degree losses):
suppose `t, r ≥ 1`, `r ≤ K < N/2` and `Q + (t + 2) r ≤ D`, and let
`η = ½ M_N(K − r)/M_N(K)`. For each line, with polynomials `u_1, …, u_s` of degree at most `r`,
there is an approximator `P_L` built from `t` factors of the form `1 + Σ_i a_i u_i` such that
`c_{P_L}(K) ≤ e^{−ηt} (h + ε M_N(K)) + 2 N² ε M_N(K) / η`.

**Formalization Note** `ℓ` odd, `N = nℓ`; `u_i` multilinear; `P_L = ML(∏_{ν<t} (1 + Σ_i a_{ν,i} u_i))`;
`h = hThresh F ℓ D K`, `ε = epsExcl n ℓ Q K`. -/
theorem proposition_4_17_approximation {n ℓ : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (D Q K r t s : ℕ) (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (hu : ∀ i, IsMultilinear (u i) ∧ (u i).totalDegree ≤ r)
    (ht : 1 ≤ t) (hr : 1 ≤ r) (hrK : r ≤ K) (hKN : 2 * K < n * ℓ) (hD : Q + (t + 2) * r ≤ D) :
    ∃ a : Fin t → Fin s → ZMod 2,
      (cErr F ℓ D K (ML (∏ ν : Fin t, (1 + ∑ i, a ν i • u i))) u : ℝ) ≤
        Real.exp (-(etaFrac (n * ℓ) K r * t)) *
            ((hThresh F ℓ D K : ℝ) + epsExcl n ℓ Q K * (monoCount (n * ℓ) K : ℝ))
          + 2 * ((n * ℓ : ℕ) : ℝ) ^ 2 * epsExcl n ℓ Q K * (monoCount (n * ℓ) K : ℝ)
            / etaFrac (n * ℓ) K r := by sorry

end AC02Frege
