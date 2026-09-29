-- Prove2me | solution 1 for syracuse_descends_below_860564
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:49:50.345853+00:00
-- url     : https://prove2.me/submissions/1b750e8d-2057-4ad4-a5cf-afa927a3dbee

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_descends_below_583288
import Theorems.Thm_syracuse_descends_range_583288_587288
import Theorems.Thm_syracuse_descends_range_587289_591289
import Theorems.Thm_syracuse_descends_range_591290_595290
import Theorems.Thm_syracuse_descends_range_595291_599291
import Theorems.Thm_syracuse_descends_range_599292_603292
import Theorems.Thm_syracuse_descends_range_603293_607293
import Theorems.Thm_syracuse_descends_range_607294_610294
import Theorems.Thm_syracuse_descends_range_610295_614295
import Theorems.Thm_syracuse_descends_range_614296_618296
import Theorems.Thm_syracuse_descends_range_618297_622297
import Theorems.Thm_syracuse_descends_range_622298_626298
import Theorems.Thm_syracuse_descends_range_626299_630299
import Theorems.Thm_syracuse_descends_range_630300_634300
import Theorems.Thm_syracuse_descends_range_634301_638301
import Theorems.Thm_syracuse_descends_range_638302_642302
import Theorems.Thm_syracuse_descends_range_642303_646303
import Theorems.Thm_syracuse_descends_range_646304_650304
import Theorems.Thm_syracuse_descends_range_650305_654305
import Theorems.Thm_syracuse_descends_range_654306_658306
import Theorems.Thm_syracuse_descends_range_658307_662307
import Theorems.Thm_syracuse_descends_range_662308_666308
import Theorems.Thm_syracuse_descends_range_666309_670309
import Theorems.Thm_syracuse_descends_range_670310_674310
import Theorems.Thm_syracuse_descends_range_674311_678311
import Theorems.Thm_syracuse_descends_range_678312_682312
import Theorems.Thm_syracuse_descends_range_682313_686313
import Theorems.Thm_syracuse_descends_range_686314_690314
import Theorems.Thm_syracuse_descends_range_690315_694315
import Theorems.Thm_syracuse_descends_range_694316_698316
import Theorems.Thm_syracuse_descends_range_698317_702317
import Theorems.Thm_syracuse_descends_range_702318_706318
import Theorems.Thm_syracuse_descends_range_706319_710319
import Theorems.Thm_syracuse_descends_range_710320_714320
import Theorems.Thm_syracuse_descends_range_714321_718321
import Theorems.Thm_syracuse_descends_range_718322_722322
import Theorems.Thm_syracuse_descends_range_722323_726323
import Theorems.Thm_syracuse_descends_range_726324_730324
import Theorems.Thm_syracuse_descends_range_730325_734325
import Theorems.Thm_syracuse_descends_range_734326_738326
import Theorems.Thm_syracuse_descends_range_738327_742327
import Theorems.Thm_syracuse_descends_range_742328_746328
import Theorems.Thm_syracuse_descends_range_746329_750329
import Theorems.Thm_syracuse_descends_range_750330_754330
import Theorems.Thm_syracuse_descends_range_754331_758331
import Theorems.Thm_syracuse_descends_range_758332_762332
import Theorems.Thm_syracuse_descends_range_762333_766333
import Theorems.Thm_syracuse_descends_range_766334_770334
import Theorems.Thm_syracuse_descends_range_770335_774335
import Theorems.Thm_syracuse_descends_range_774336_778336
import Theorems.Thm_syracuse_descends_range_778337_782337
import Theorems.Thm_syracuse_descends_range_782338_786338
import Theorems.Thm_syracuse_descends_range_786339_790339
import Theorems.Thm_syracuse_descends_range_790340_794340
import Theorems.Thm_syracuse_descends_range_794341_798341
import Theorems.Thm_syracuse_descends_range_798342_802342
import Theorems.Thm_syracuse_descends_range_802343_806343
import Theorems.Thm_syracuse_descends_range_806344_810344
import Theorems.Thm_syracuse_descends_range_810345_814345
import Theorems.Thm_syracuse_descends_range_814346_818346
import Theorems.Thm_syracuse_descends_range_818347_822347
import Theorems.Thm_syracuse_descends_range_822348_826348
import Theorems.Thm_syracuse_descends_range_826349_830349
import Theorems.Thm_syracuse_descends_range_830350_834350
import Theorems.Thm_syracuse_descends_range_834351_838351
import Theorems.Thm_syracuse_descends_range_838352_842352
import Theorems.Thm_syracuse_descends_range_842353_846353
import Theorems.Thm_syracuse_descends_range_846354_850354
import Theorems.Thm_syracuse_descends_range_850355_854355
import Theorems.Thm_syracuse_descends_range_854356_858356
import Theorems.Thm_syracuse_descends_range_858357_860563

theorem solution (m : ℕ) (h1 : 1 < m) (hlt : m < 860564) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  rcases Nat.lt_or_ge m 583288 with hb | hb
  · exact syracuse_descends_below_583288 m h1 hb hodd
  rcases Nat.lt_or_ge m 587289 with hc0 | hc0
  · exact syracuse_descends_range_583288_587288 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 591290 with hc1 | hc1
  · exact syracuse_descends_range_587289_591289 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 595291 with hc2 | hc2
  · exact syracuse_descends_range_591290_595290 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 599292 with hc3 | hc3
  · exact syracuse_descends_range_595291_599291 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 603293 with hc4 | hc4
  · exact syracuse_descends_range_599292_603292 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 607294 with hc5 | hc5
  · exact syracuse_descends_range_603293_607293 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 610295 with hc6 | hc6
  · exact syracuse_descends_range_607294_610294 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 614296 with hc7 | hc7
  · exact syracuse_descends_range_610295_614295 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 618297 with hc8 | hc8
  · exact syracuse_descends_range_614296_618296 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 622298 with hc9 | hc9
  · exact syracuse_descends_range_618297_622297 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 626299 with hc10 | hc10
  · exact syracuse_descends_range_622298_626298 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 630300 with hc11 | hc11
  · exact syracuse_descends_range_626299_630299 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 634301 with hc12 | hc12
  · exact syracuse_descends_range_630300_634300 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 638302 with hc13 | hc13
  · exact syracuse_descends_range_634301_638301 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 642303 with hc14 | hc14
  · exact syracuse_descends_range_638302_642302 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 646304 with hc15 | hc15
  · exact syracuse_descends_range_642303_646303 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 650305 with hc16 | hc16
  · exact syracuse_descends_range_646304_650304 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 654306 with hc17 | hc17
  · exact syracuse_descends_range_650305_654305 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 658307 with hc18 | hc18
  · exact syracuse_descends_range_654306_658306 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 662308 with hc19 | hc19
  · exact syracuse_descends_range_658307_662307 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 666309 with hc20 | hc20
  · exact syracuse_descends_range_662308_666308 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 670310 with hc21 | hc21
  · exact syracuse_descends_range_666309_670309 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 674311 with hc22 | hc22
  · exact syracuse_descends_range_670310_674310 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 678312 with hc23 | hc23
  · exact syracuse_descends_range_674311_678311 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 682313 with hc24 | hc24
  · exact syracuse_descends_range_678312_682312 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 686314 with hc25 | hc25
  · exact syracuse_descends_range_682313_686313 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 690315 with hc26 | hc26
  · exact syracuse_descends_range_686314_690314 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 694316 with hc27 | hc27
  · exact syracuse_descends_range_690315_694315 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 698317 with hc28 | hc28
  · exact syracuse_descends_range_694316_698316 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 702318 with hc29 | hc29
  · exact syracuse_descends_range_698317_702317 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 706319 with hc30 | hc30
  · exact syracuse_descends_range_702318_706318 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 710320 with hc31 | hc31
  · exact syracuse_descends_range_706319_710319 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 714321 with hc32 | hc32
  · exact syracuse_descends_range_710320_714320 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 718322 with hc33 | hc33
  · exact syracuse_descends_range_714321_718321 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 722323 with hc34 | hc34
  · exact syracuse_descends_range_718322_722322 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 726324 with hc35 | hc35
  · exact syracuse_descends_range_722323_726323 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 730325 with hc36 | hc36
  · exact syracuse_descends_range_726324_730324 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 734326 with hc37 | hc37
  · exact syracuse_descends_range_730325_734325 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 738327 with hc38 | hc38
  · exact syracuse_descends_range_734326_738326 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 742328 with hc39 | hc39
  · exact syracuse_descends_range_738327_742327 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 746329 with hc40 | hc40
  · exact syracuse_descends_range_742328_746328 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 750330 with hc41 | hc41
  · exact syracuse_descends_range_746329_750329 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 754331 with hc42 | hc42
  · exact syracuse_descends_range_750330_754330 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 758332 with hc43 | hc43
  · exact syracuse_descends_range_754331_758331 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 762333 with hc44 | hc44
  · exact syracuse_descends_range_758332_762332 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 766334 with hc45 | hc45
  · exact syracuse_descends_range_762333_766333 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 770335 with hc46 | hc46
  · exact syracuse_descends_range_766334_770334 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 774336 with hc47 | hc47
  · exact syracuse_descends_range_770335_774335 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 778337 with hc48 | hc48
  · exact syracuse_descends_range_774336_778336 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 782338 with hc49 | hc49
  · exact syracuse_descends_range_778337_782337 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 786339 with hc50 | hc50
  · exact syracuse_descends_range_782338_786338 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 790340 with hc51 | hc51
  · exact syracuse_descends_range_786339_790339 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 794341 with hc52 | hc52
  · exact syracuse_descends_range_790340_794340 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 798342 with hc53 | hc53
  · exact syracuse_descends_range_794341_798341 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 802343 with hc54 | hc54
  · exact syracuse_descends_range_798342_802342 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 806344 with hc55 | hc55
  · exact syracuse_descends_range_802343_806343 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 810345 with hc56 | hc56
  · exact syracuse_descends_range_806344_810344 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 814346 with hc57 | hc57
  · exact syracuse_descends_range_810345_814345 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 818347 with hc58 | hc58
  · exact syracuse_descends_range_814346_818346 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 822348 with hc59 | hc59
  · exact syracuse_descends_range_818347_822347 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 826349 with hc60 | hc60
  · exact syracuse_descends_range_822348_826348 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 830350 with hc61 | hc61
  · exact syracuse_descends_range_826349_830349 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 834351 with hc62 | hc62
  · exact syracuse_descends_range_830350_834350 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 838352 with hc63 | hc63
  · exact syracuse_descends_range_834351_838351 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 842353 with hc64 | hc64
  · exact syracuse_descends_range_838352_842352 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 846354 with hc65 | hc65
  · exact syracuse_descends_range_842353_846353 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 850355 with hc66 | hc66
  · exact syracuse_descends_range_846354_850354 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 854356 with hc67 | hc67
  · exact syracuse_descends_range_850355_854355 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 858357 with hc68 | hc68
  · exact syracuse_descends_range_854356_858356 m (by omega) (by omega) hodd
  exact syracuse_descends_range_858357_860563 m (by omega) (by omega) hodd
