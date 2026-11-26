-- Prove2me | Theorems.Thm_Erdos287_proth_prime_certificate
-- name    : Erdos287.proth_prime_certificate
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T09:34:45.750797+00:00
-- url     : https://prove2.me/theorems/e96da43a-a058-4d2c-a562-0596e2054eeb
-- title:
--   Proth primality certificate from a single modular power
-- statement:
--   Let \(k,e,g\) be natural numbers with \(0<k<2^{e+1}\). Put \(n=k2^{e+1}+1\). If \(g^{k2^e}\equiv-1\pmod n\), then \(n\) is prime.
-- source:
--   Proth, Théorèmes sur les nombres premiers, Comptes rendus 87 (1878), 926–927. https://fr.wikisource.org/wiki/Page:Comptes_rendus_hebdomadaires_des_séances_de_l’Académie_des_sciences,_tome_087,_1878.djvu/932. Application to Erdős Problem 287.

import Mathlib

theorem Erdos287.proth_prime_certificate (k e g : ℕ) (hk : 0 < k) (hsmall : k < 2 ^ (e + 1))
    (hg : (g : ZMod (k * 2 ^ (e + 1) + 1)) ^ (k * 2 ^ e) = -1) :
    (k * 2 ^ (e + 1) + 1).Prime := by sorry
