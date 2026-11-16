-- Prove2me | Theorems.Thm_CKKSPrecision_FourierUnits_Supplement_lemma_7_2
-- name    : CKKSPrecision.FourierUnits.Supplement.lemma_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:26:39.753211+00:00
-- url     : https://prove2.me/theorems/54325873-cab0-45eb-968a-6acf1d8398c3
-- title:
--   Lemma 7.2 — error after multiplication and rescaling
-- statement:
--   Let $r\ge1$ be a power of two and $p\ne0$ lie in $R$. Two ciphertexts share an odd modulus $Q=DQ'$ and secret key $s\in R$, with positive scales $\Delta_a,\Delta_b$, $Q'>1$ and odd $D>1$. Suppose their restored messages $M_a,M_b$ represent logical inputs $x_a,x_b$ with errors $e_{a,j}=\sigma_j(p)\eta_{a,j}$ and $e_{b,j}=\sigma_j(p)\eta_{b,j}$. Assume
--   $$
--   |x_{a,j}|\le A_{a,j},\quad |x_{b,j}|\le A_{b,j},\quad
--   |\eta_{a,j}|\le B_{a,j},\quad |\eta_{b,j}|\le B_{b,j}.
--   $$
--   Relinearize the componentwise $p$-corrected tensor product, with phase error $\kappa$ satisfying $|\sigma_j(\kappa)|\le K$. Let $\rho_0,\rho_1$ be the actual residues of this relinearized ciphertext modulo $D$, and assume $|\sigma_j(\rho_0+\rho_1s)|\le R_0$. After rescaling, set $\Delta_v=\Delta_a\Delta_b/D$ and compute the restored message by (17). Its logical value is $x_{v,j}=x_{a,j}x_{b,j}$. With
--   $$
--   B_{v,j}=A_{a,j}B_{b,j}+A_{b,j}B_{a,j}
--    +|\sigma_j(p)|B_{a,j}B_{b,j}+\frac{K+R_0}{D\Delta_v},
--   $$
--   its restored and normalized errors satisfy
--   $$
--   |e_{v,j}|\le|\sigma_j(p)|B_{v,j},\qquad
--    e_{v,j}=\sigma_j(p)\eta_{v,j},\qquad |\eta_{v,j}|\le B_{v,j}
--   $$
--   for every slot. In particular, the parenthesized expression in (20) is a valid normalized error bound.
--
--   This is the multiplication-and-rescaling error rule used by the circuit induction.
--
--   Differences from the source:
--   - encoding: the CKKS cyclotomic ring and selected embeddings in power-of-two dimension, with ciphertext components in R_Q → the published field and integral subalgebra, Fin r slots, an explicit power-of-two hypothesis and integral representatives with congruence modulo Q; reason: these are the same ring, cyclic embedding order and quotient classes, including r=1; field expressions carry explicit integral-ring membership and the operations choose the prescribed representatives
--   - generalization: the rational scale and bound data chosen for the allocation algorithm, with a unit multiplier → arbitrary positive real scales and real bounds, with any nonzero integral multiplier; reason: the expansion and triangle inequalities in the proof of Lemma 7.2 require only positivity of scales and nonzero p; all rational-data unit instances of the source are recovered
--   - encoding: the output logical product and its restored and normalized errors → the logical product and rescaled restored polynomial are computed, and the errors are their embedding discrepancies; reason: this fixes the operation in (19) rather than assuming an arbitrary output error; the standing nonzero multiplier makes normalized division valid
-- source:
--   Zhaoyang Liang, Runkun Liu, Jingwei Fang, Dan Ding, STOC 2027 submission #148 (October 2026), p. 15 (PDF p. 17), Lemma 7.2, (18)–(20); proof p. 25 (PDF p. 27).

import Definitions.Def_CKKSPrecision_FourierUnits_Supplement_ckks_model

set_option autoImplicit false

namespace CKKSPrecision.FourierUnits.Supplement

theorem lemma_7_2 (r : ℕ+) (hr : ∃ k : ℕ, (r : ℕ) = 2 ^ k)
    (q q' d : ℕ) (hq : 1 < q) (hqodd : Odd q) (hq' : 1 < q')
    (hd : 1 < d) (hdodd : Odd d) (hqd : q = d * q')
    (da db : ℝ) (hda : 0 < da) (hdb : 0 < db)
    (p s ma mb kappa : Scalar r) (hp : InRing p) (hp0 : p ≠ 0) (hs : InRing s)
    (ca cb relin : Cipher r) (hca : IntegralCipher ca) (hcb : IntegralCipher cb)
    (xa xb etaa etab : Vector r)
    (ha : Represented q da p s ca ma xa (fun j => sigma p j * etaa j))
    (hb : Represented q db p s cb mb xb (fun j => sigma p j * etab j))
    (hrel : Relin q p s ca cb relin kappa)
    (aa ab ba bb : Slot r → ℝ) (kb rb : ℝ)
    (hbound : ∀ j, ‖xa j‖ ≤ aa j ∧ ‖xb j‖ ≤ ab j ∧ ‖etaa j‖ ≤ ba j ∧ ‖etab j‖ ≤ bb j)
    (hprimitive : ∀ j, ‖sigma kappa j‖ ≤ kb ∧ ‖sigma (phase s (residues d relin)) j‖ ≤ rb) :
    let delta := da * db / d
    let xv : Vector r := fun j => xa j * xb j
    let mv := rescaledMessage d p s (ma * mb + p * kappa) relin
    let ev := restoredError delta mv xv
    let etav := normalizedError delta p mv xv
    (∀ j, xv j = xa j * xb j) ∧
      (∀ j, ‖ev j‖ ≤ ‖sigma p j‖ * multiplicationBound p aa ab ba bb kb rb d delta j) ∧
      (∀ j, ev j = sigma p j * etav j ∧
        ‖etav j‖ ≤ multiplicationBound p aa ab ba bb kb rb d delta j) := by sorry

end CKKSPrecision.FourierUnits.Supplement
