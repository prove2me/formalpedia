-- Prove2me | solution 1 for mme_stothers_remaining_four_type2_marginal_determinacy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:10:36.639767+00:00
-- url     : https://prove2.me/submissions/6019c20f-f73f-4d39-b065-ac50ab73e5fc

import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace MME.StothersFourth.RemainingFour

/-- The `phi_125` mode-2 and mode-3 marginal data determine its three
profile parameters. -/
theorem phi125_marginals_injective
    (a b c a' b' c' : ℕ)
    (hac : a + c = a' + c')
    (hb : 2 * b = 2 * b')
    (ha : a = a')
    (_hbc : b + c = b' + c') :
    a = a' ∧ b = b' ∧ c = c' := by
  omega

/-- The `phi_134` mode-2 and mode-3 marginal data determine its four
profile parameters. -/
theorem phi134_marginals_injective
    (a b c d a' b' c' d' : ℕ)
    (had : a + d = a' + d')
    (hbc : b + c = b' + c')
    (ha : a = a')
    (hbd : b + d = b' + d')
    (_hc : 2 * c = 2 * c') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  omega

/-- The `phi_224` three-mode marginal data determine its four profile
parameters. -/
theorem phi224_marginals_injective
    (a b c d a' b' c' d' : ℕ)
    (habc : a + b + c = a' + b' + c')
    (ha : a = a')
    (hb : 2 * b = 2 * b')
    (hcd : 2 * c + 2 * d = 2 * c' + 2 * d') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  omega

/-- For `phi_233`, equal full marginals are equivalent to equality of the
two aggregate parameters `sigma = 2a+b` and `mu = a+c`.  This identifies
exactly the nontrivial profile fiber that remains in Lemma 5.1(v). -/
theorem phi233_same_marginals_iff_same_sigma_mu
    (N a b c d a' b' c' d' : ℕ)
    (hsum : 2 * a + b + c + d = N)
    (hsum' : 2 * a' + b' + c' + d' = N) :
    (2 * a + b = 2 * a' + b' ∧
      2 * c + 2 * d = 2 * c' + 2 * d' ∧
      a + c = a' + c' ∧
      a + b + d = a' + b' + d') ↔
    (2 * a + b = 2 * a' + b' ∧ a + c = a' + c') := by
  constructor
  · exact fun h ↦ ⟨h.1, h.2.2.1⟩
  · rintro ⟨hsigma, hmu⟩
    omega

end MME.StothersFourth.RemainingFour

theorem solution :
    (∀ a b c a' b' c' : ℕ,
      a + c = a' + c' →
      2 * b = 2 * b' →
      a = a' →
      b + c = b' + c' →
      a = a' ∧ b = b' ∧ c = c') ∧
    (∀ a b c d a' b' c' d' : ℕ,
      a + d = a' + d' →
      b + c = b' + c' →
      a = a' →
      b + d = b' + d' →
      2 * c = 2 * c' →
      a = a' ∧ b = b' ∧ c = c' ∧ d = d') ∧
    (∀ a b c d a' b' c' d' : ℕ,
      a + b + c = a' + b' + c' →
      a = a' →
      2 * b = 2 * b' →
      2 * c + 2 * d = 2 * c' + 2 * d' →
      a = a' ∧ b = b' ∧ c = c' ∧ d = d') ∧
    (∀ N a b c d a' b' c' d' : ℕ,
      2 * a + b + c + d = N →
      2 * a' + b' + c' + d' = N →
      ((2 * a + b = 2 * a' + b' ∧
          2 * c + 2 * d = 2 * c' + 2 * d' ∧
          a + c = a' + c' ∧
          a + b + d = a' + b' + d') ↔
        (2 * a + b = 2 * a' + b' ∧ a + c = a' + c'))) := by
  exact ⟨
    fun a b c a' b' c' ↦
      MME.StothersFourth.RemainingFour.phi125_marginals_injective a b c a' b' c',
    fun a b c d a' b' c' d' ↦
      MME.StothersFourth.RemainingFour.phi134_marginals_injective a b c d a' b' c' d',
    fun a b c d a' b' c' d' ↦
      MME.StothersFourth.RemainingFour.phi224_marginals_injective a b c d a' b' c' d',
    fun N a b c d a' b' c' d' ↦
      MME.StothersFourth.RemainingFour.phi233_same_marginals_iff_same_sigma_mu
        N a b c d a' b' c' d'
  ⟩
