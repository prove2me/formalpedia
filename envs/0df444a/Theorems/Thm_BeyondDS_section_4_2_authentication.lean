-- Prove2me | Theorems.Thm_BeyondDS_section_4_2_authentication
-- name    : BeyondDS.section_4_2_authentication
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:14:56.802726+00:00
-- url     : https://prove2.me/theorems/099d1bfd-04df-4d3c-af22-92c1c16bfc43
-- title:
--   §4.2 — the authentication event fails with negligible probability under EUF-CMA
-- statement:
--   Let $(\Sigma_\kappa)$ be an efficient, perfectly correct family of signature schemes that is EUF-CMA secure against non-uniform PPT forgers, let $\Pi$ be any efficient protocol, let the parameters $(t_\kappa,\lambda_\kappa)$ be polynomially bounded in $\kappa$ (with any senders and input bits), and let the adversary be a non-uniform PPT reactive machine family. Then the probability of the forgery event over the whole execution at parameter $\kappa$ is negligible in $\kappa$.
--
--   This is §4.2's "The authentication event says that any verifying data attributed to a currently uncorrupted player were signed by that player. … Its complement has probability at most $\epsilon_{sig}$ over the entire execution under the applicable signature security assumption." The paper states it and gives no reduction. It is what turns the bounds stated in terms of $\epsilon$ into $\mathrm{negl}(\kappa)$ terms.
--
--   Differences from the source:
--
--   - generalization: the protocols of the paper → every efficient protocol; reason: the reduction uses only the efficiency of the protocol, and the compiler is an instance
--   - reading: "the applicable signature security assumption" → EUF-CMA with perfect correctness against non-uniform probabilistic polynomial-time forgers, with a non-uniform PPT adversary; reason: p.22, "no strong-unforgeability assumption is needed"; non-uniformity on both sides is what composes with arbitrary parameter families (decisions 7–8)
--   - reading: "including this post-erasure guarantee when required" → no erasure clause; reason: erasures belong to the alternative of Section 10 and are not required for Theorem 1
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), §4.2, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_BeyondDS_DeliveryFail
import Definitions.Def_BeyondDS_EUFCMA

set_option autoImplicit false

open QAlgorithms.Complexity
open scoped ENNReal
open Polynomial

namespace BeyondDS

/-- The authentication bound of Rambaud, *Beyond Dolev–Strong*, STOC 2027 submission (manuscript sha256 c84cf9c9…), §4.2, p.12 (PDF 13): "The authentication event says that any verifying data attributed to a currently uncorrupted player were signed by that player. […] Its complement has probability at most ϵsig over the entire execution under the applicable signature security assumption". For an efficient, perfectly correct family unforgeable under chosen-message attacks,
any efficient protocol, polynomially bounded parameters and a non-uniform probabilistic polynomial-time adversary, the forgery probability over the whole execution is negligible in `κ`.

**Formalization Note.** The paper states this and gives no reduction. Erasures belong to Section 10 and do not occur. This is what turns the bounds in terms of `ϵ` into `negl(κ)`. It holds for every efficient protocol, and not only for the compiler. -/
theorem section_4_2_authentication (Sg : ℕ → Sig) (hEff : SigFamilyEfficient Sg) (hCor : ∀ κ, (Sg κ).Correct) (hSec : EUFCMA Sg)
    (Pi : Protocol Str Str) (p : ℕ[X]) (hPi : IsEfficientProtocol Pi p) (Pf : ℕ → Params) (hκ : ∀ κ, (Pf κ).κ = κ)
    (q : ℕ[X]) (hPoly : ∀ κ, (Pf κ).t + (Pf κ).lam ≤ q.eval κ) (X : ℕ → Bool) (R : ReactiveFamily) (hR : R.Valid) :
    ∃ ν, Negligible ν ∧ ∀ κ,
      prob (exec Pi (Sg κ) (Pf κ) (X κ) (uniformElect (Pf κ)) (R.toAdversary κ (Pf κ).n)) {ω | Forge ω} ≤
        ENNReal.ofReal (ν κ) := by sorry

end BeyondDS
