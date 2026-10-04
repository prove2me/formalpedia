-- Prove2me | Theorems.Thm_ErdosStraus242_hard_core_840_after_68_sieves
-- name    : ErdosStraus242.hard_core_840_after_68_sieves
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-04T09:28:37.994979+00:00
-- url     : https://prove2.me/theorems/028f6196-5c32-4b4f-8367-7b76c17a4a0e
-- title:
--   Remaining modulo-840 prime cases after the sixty-eight congruence families
-- statement:
--   Let $p>2$ be prime. Assume $p\bmod840\in\{1,121,169,289,361,529\}$ and that $p$ avoids the excluded residue classes modulo each of the 68 listed moduli: 11, 19, 23, 31, 43, 47, 59, 67, 71, 79, 83, 103, 107, 127, 131, 139, 143, 151, 163, 167, 179, 187, 191, 199, 211, 223, 227, 239, 247, 251, 263, 271, 283, 299, 307, 311, 319, 323, 331, 347, 359, 367, 379, 383, 391, 403, 407, 419, 431, 439, 443, 451, 463, 467, 487, 491, 499, 503, 523, 527, 547, 551, 559, 563, 571, 583, 587, 599. The remaining assertion is that there are natural numbers $1\le x<y<z$ with $4/p=1/x+1/y+1/z$ in $\mathbb Q$. This is the open residual frontier of Erdős Problem 242, obtained from `ErdosStraus242.hard_core_840_after_48_sieves` by removing the twenty families `family_mod187` … `family_mod599` (all moduli $\equiv3\pmod4$, coprime to $840$, below $600$ that were unsieved). Together with those proved families it recovers the previous frontier; the strict denominator convention is retained. (This resubmission fixes the theorem name inside the formal statement, which a previous job rejected.)
-- source:
--   Erdős Problem 242, https://www.erdosproblems.com/242, restricted from the mission frontier ErdosStraus242.hard_core_840_after_48_sieves. The twenty additional exclusions come from the Bloom–Elsholtz $a=1$ parametrization classes at the moduli 187, 247, 391, 403, 451, 463, 487, 491, 499, 503, 523, 527, 547, 551, 559, 563, 571, 583, 587, 599, p. 239, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf. This residual formulation is a decomposition made here, not a quoted result.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem hard_core_840_after_68_sieves (p : ℕ) (hp : Nat.Prime p) (hp2 : 2 < p)
    (hres : p % 840 ∈ ({1, 121, 169, 289, 361, 529} : Finset ℕ))
    (h11 : p % 11 ∉ ({7, 8, 10} : Finset ℕ))
    (h19 : p % 19 ∉ ({14, 15, 18} : Finset ℕ))
    (h23 : p % 23 ∉ ({7, 10, 11, 15, 17, 19, 20, 21, 22} : Finset ℕ))
    (h31 : p % 31 ∉ ({23, 27} : Finset ℕ))
    (h43 : p % 43 ∉ ({39} : Finset ℕ))
    (h47 : p % 47 ∉ ({35} : Finset ℕ))
    (h59 : p % 59 ∉ ({47} : Finset ℕ))
    (h67 : p % 67 ∉ ({63} : Finset ℕ))
    (h71 : p % 71 ∉ ({59} : Finset ℕ))
    (h79 : p % 79 ∉ ({39, 59, 63, 71, 75} : Finset ℕ))
    (h83 : p % 83 ∉ ({55} : Finset ℕ))
    (h103 : p % 103 ∉ ({99, 95, 51} : Finset ℕ))
    (h107 : p % 107 ∉ ({71} : Finset ℕ))
    (h127 : p % 127 ∉ ({123, 119, 111, 95, 63} : Finset ℕ))
    (h131 : p % 131 ∉ ({119} : Finset ℕ))
    (h139 : p % 139 ∉ ({111} : Finset ℕ))
    (h143 : p % 143 ∉ ({71, 95, 107, 119, 127, 131, 135, 139} : Finset ℕ))
    (h151 : p % 151 ∉ ({143} : Finset ℕ))
    (h163 : p % 163 ∉ ({159} : Finset ℕ))
    (h167 : p % 167 ∉ ({163} : Finset ℕ))
    (h179 : p % 179 ∉ ({119} : Finset ℕ))
    (h187 : p % 187 ∉ ({183} : Finset ℕ))
    (h191 : p % 191 ∉ ({127} : Finset ℕ))
    (h199 : p % 199 ∉ ({179} : Finset ℕ))
    (h211 : p % 211 ∉ ({207} : Finset ℕ))
    (h223 : p % 223 ∉ ({215} : Finset ℕ))
    (h227 : p % 227 ∉ ({151} : Finset ℕ))
    (h239 : p % 239 ∉ ({231} : Finset ℕ))
    (h247 : p % 247 ∉ ({243, 239, 123} : Finset ℕ))
    (h251 : p % 251 ∉ ({167} : Finset ℕ))
    (h263 : p % 263 ∉ ({255} : Finset ℕ))
    (h271 : p % 271 ∉ ({267} : Finset ℕ))
    (h283 : p % 283 ∉ ({279} : Finset ℕ))
    (h299 : p % 299 ∉ ({295, 287, 279, 239, 199} : Finset ℕ))
    (h307 : p % 307 ∉ ({263} : Finset ℕ))
    (h311 : p % 311 ∉ ({259} : Finset ℕ))
    (h319 : p % 319 ∉ ({315, 311, 303, 299, 287, 279, 255, 239, 159} : Finset ℕ))
    (h323 : p % 323 ∉ ({319, 311, 287, 215} : Finset ℕ))
    (h331 : p % 331 ∉ ({327} : Finset ℕ))
    (h347 : p % 347 ∉ ({335} : Finset ℕ))
    (h359 : p % 359 ∉ ({323} : Finset ℕ))
    (h367 : p % 367 ∉ ({363} : Finset ℕ))
    (h379 : p % 379 ∉ ({303} : Finset ℕ))
    (h383 : p % 383 ∉ ({311} : Finset ℕ))
    (h391 : p % 391 ∉ ({387, 383, 363, 335, 195} : Finset ℕ))
    (h403 : p % 403 ∉ ({399} : Finset ℕ))
    (h407 : p % 407 ∉ ({403, 399, 395, 383, 339, 271, 203} : Finset ℕ))
    (h419 : p % 419 ∉ ({391} : Finset ℕ))
    (h431 : p % 431 ∉ ({407} : Finset ℕ))
    (h439 : p % 439 ∉ ({419} : Finset ℕ))
    (h443 : p % 443 ∉ ({431} : Finset ℕ))
    (h451 : p % 451 ∉ ({447} : Finset ℕ))
    (h463 : p % 463 ∉ ({459, 455, 447, 347, 231} : Finset ℕ))
    (h467 : p % 467 ∉ ({463} : Finset ℕ))
    (h487 : p % 487 ∉ ({483, 479, 243} : Finset ℕ))
    (h491 : p % 491 ∉ ({487, 479, 327} : Finset ℕ))
    (h499 : p % 499 ∉ ({495, 479, 399} : Finset ℕ))
    (h503 : p % 503 ∉ ({499, 495, 491, 479, 475, 467, 447, 431, 419, 335, 251} : Finset ℕ))
    (h523 : p % 523 ∉ ({519} : Finset ℕ))
    (h527 : p % 527 ∉ ({523, 519, 515, 511, 503, 483, 479, 439, 395, 351, 263} : Finset ℕ))
    (h547 : p % 547 ∉ ({543} : Finset ℕ))
    (h551 : p % 551 ∉ ({547, 543, 539, 527, 459, 367, 275} : Finset ℕ))
    (h559 : p % 559 ∉ ({555, 551, 543, 539, 531, 519, 503, 479, 447, 419, 279} : Finset ℕ))
    (h563 : p % 563 ∉ ({559, 551, 375} : Finset ℕ))
    (h571 : p % 571 ∉ ({567, 527, 519} : Finset ℕ))
    (h583 : p % 583 ∉ ({579, 575, 291} : Finset ℕ))
    (h587 : p % 587 ∉ ({583, 575, 559, 503, 391} : Finset ℕ))
    (h599 : p % 599 ∉ ({595, 591, 587, 579, 575, 559, 539, 499, 479, 399, 299} : Finset ℕ))
    : IsErdosStraus p := by sorry
end ErdosStraus242
