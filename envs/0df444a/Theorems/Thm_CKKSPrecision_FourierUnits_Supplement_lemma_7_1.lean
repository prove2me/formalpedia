-- Prove2me | Theorems.Thm_CKKSPrecision_FourierUnits_Supplement_lemma_7_1
-- name    : CKKSPrecision.FourierUnits.Supplement.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:25:53.590478+00:00
-- url     : https://prove2.me/theorems/54f6d011-7ab0-4ead-bbee-261c31323414
-- title:
--   Lemma 7.1 — preservation under rescaling
-- statement:
--   Let $r\ge1$ be a power of two, $Q=DQ'$ an odd modulus with $Q'>1$, and $D>1$ odd. Let $\Delta>0$, $p,s\in R$ and let $\mathrm{ct}=(c_0,c_1)$ have integral representatives. Suppose $M\in R$ satisfies
--   $$
--   p(c_0+c_1s)\equiv M\pmod Q,\qquad \sigma_j(M)=\Delta(x_j+e_j).
--   $$
--   Put $\rho_i=[c_i]_D$, $c_i'=[(c_i-\rho_i)/D]_{Q'}$, $\Delta'=\Delta/D$ and
--   $$
--   M'=\frac{M-p(\rho_0+\rho_1s)}D.
--   $$
--   Then the numerator is divisible by $D$ in $R$, $M'\in R$, and
--   $$
--   p(c_0'+c_1's)\equiv M'\pmod {Q'},\qquad
--   \frac{\sigma_j(M')}{\Delta'}=x_j+e_j-
--   \frac{\sigma_j(p)\sigma_j(\rho_0+\rho_1s)}{D\Delta'}
--   $$
--   for every slot $j$. No invertibility or nonzero assumption on $p$ and no centering of the input phase is needed.
--
--   The result preserves the restored representation during the rescaling operations used in the circuit bound.
--
--   Differences from the source:
--   - encoding: the CKKS cyclotomic ring and selected embeddings in power-of-two dimension, with ciphertext components in R_Q → the published field and integral subalgebra, Fin r slots, an explicit power-of-two hypothesis and integral representatives with congruence modulo Q; reason: these are the same ring, cyclic embedding order and quotient classes, including r=1; field expressions carry explicit integral-ring membership and the operations choose the prescribed representatives
--   - generalization: the standing nonzero multiplier in the surrounding scheme → an arbitrary integral p, including p=0; reason: the divisibility, congruence and embedding identities in the proof of Lemma 7.1 use no inverse of p and remain valid at zero
--   - encoding: the integral quotient in (17) belongs to R → the quotient is computed in K and its membership in R and divisibility in R are conclusions; reason: division is total in Lean; D>1 excludes zero and the conclusions recover exactly the integral polynomial
-- source:
--   Zhaoyang Liang, Runkun Liu, Jingwei Fang, Dan Ding, STOC 2027 submission #148 (October 2026), p. 14 (PDF p. 16), Lemma 7.1 and (17); proof p. 24 (PDF p. 26).

import Definitions.Def_CKKSPrecision_FourierUnits_Supplement_ckks_model

set_option autoImplicit false

namespace CKKSPrecision.FourierUnits.Supplement

theorem lemma_7_1 (r : ℕ+) (hr : ∃ k : ℕ, (r : ℕ) = 2 ^ k)
    (q q' d : ℕ) (hq : 1 < q) (hqodd : Odd q) (hq' : 1 < q')
    (hd : 1 < d) (hdodd : Odd d) (hqd : q = d * q')
    (delta : ℝ) (hdelta : 0 < delta) (p s m : Scalar r)
    (hp : InRing p) (hs : InRing s) (ct : Cipher r) (hct : IntegralCipher ct)
    (x e : Vector r) (hrep : Represented q delta p s ct m x e) :
    let m' := rescaledMessage d p s m ct
    let ct' := rescale d q' ct
    let delta' := delta / d
    InRing m' ∧
      (∃ z : Scalar r, InRing z ∧ m - p * phase s (residues d ct) = (d : Scalar r) * z) ∧
      Congruent q' (p * phase s ct') m' ∧
      ∀ j, sigma m' j / (delta' : ℂ) = x j +
        (e j - sigma p j * sigma (phase s (residues d ct)) j / ((d : ℂ) * (delta' : ℂ))) := by sorry

end CKKSPrecision.FourierUnits.Supplement
